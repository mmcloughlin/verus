//! This module transforms the original code (with exec + proof + spec code)
//! into an abstracted version of the code (with only exec + proof code, no spec code)
//! for the purpose of checking ownership/lifetime/borrow on the exec and proof code.
//! (All spec code is erased because no ownership/lifetime/borrow checking should be
//! performed on spec code.)
//! This module then feeds the transformed code to rustc so that rustc can
//! catch any ownership/lifetime/borrow errors.

/*
The generated abstracted code discards much of the detail of the original code,
but keeps enough for ownership/lifetime/borrow checking.
Specifically it keeps:
- struct and enum declarations, and fields of the declarations
- lifetime ('a) and type (A) parameters, but not trait bounds (except for Copy, which is kept)
- functions, with impl methods turned into to top-level functions
- function bodies, but with external_body function bodies replaced with panic
  (external functions are erased completely)
- overall structure of blocks, statements, and expressions, but with specific operators
  transformed into calls to a generic function named "op"
- variable declarations and pattern matching
(The exact program elements that are kept can be seen in the abstract syntax defined in lifetime_ast.rs.)
For example, if the original code is the following:

    struct S {
    }

    spec fn fspec(i: u32, s1: S, s2: S) -> u32 {
        i
    }

    proof fn fproof(i: u32, tracked s1: S, tracked s2: S) -> u32 {
        i
    }

    fn fexec(i: u32, s1: S, s2: S) -> u32 {
        i
    }

    proof fn test_proof(i: u32, tracked s: S) {
        let j = fspec(i, s, s);
        let k = fproof(i, s, s);
    }

    fn test_exec(i: u32, s: S)
        requires i < 100
    {
        proof {
            let j = fspec(i, s, s);
            let k = fproof(i, s, s);
        }
        let k = fexec(i, s, s);
        let n = fexec(i, s, s);
    }

Then the generated "synthetic" Rust code will look like the following
(use the --log-all or --log-lifetime options to print the generated synthetic code
to a file in the .verus-log directory):

    struct D1_S {
    }

    fn f3_fproof(
        x4_i: (),
        x5_s1: D1_S,
        x6_s2: D1_S,
    )
    {
    }

    fn f8_fexec(
        x4_i: u32,
        x5_s1: D1_S,
        x6_s2: D1_S,
    ) -> u32
    {
        x4_i
    }

    fn f11_test_proof(
        x4_i: (),
        x9_s: D1_S,
    )
    {
        f3_fproof(op::<_, ()>(()), x9_s, x9_s, );
    }

    fn f15_test_exec(
        x4_i: u32,
        x9_s: D1_S,
    )
    {
        {
            f3_fproof(op::<_, ()>(()), x9_s, x9_s, );
        };
        let x12_k: u32 = f8_fexec(x4_i, x9_s, x9_s, );
        let x13_n: u32 = f8_fexec(x4_i, x9_s, x9_s, );
    }

When rustc is called on this generated code, rustc will report ownership violations
because the code tries to duplicate the linear variable "x9_s", which
corresponds to "s" in the original code.

When we print the error messages, we need to transform the line and column numbers
so that the error messages correspond to the original code.
These error messages are generated by running rustc on the synthetic code,
with rustc configured to generate errors in JSON format, capturing the JSON errors
and parsing them to retrieve the line/column information and error messages,
converting the synthetic line/column information back into spans for the original source code,
and then sending the error messages and spans to the rustc diagnostics for the original source code.
*/

use crate::erase::ErasureHints;
use crate::lifetime_emit::*;
use crate::lifetime_generate::*;
use crate::spans::SpanContext;
use crate::util::error;
use crate::verus_items::VerusItems;
use rustc_hir::{AssocItemKind, Crate, ItemKind, MaybeOwner, OwnerNode};
use rustc_middle::mir::BorrowCheckResult;
use rustc_middle::ty::TyCtxt;
use serde::Deserialize;
use std::fs::File;
use std::io::Write;
use vir::ast::VirErr;
use vir::messages::{message_bare, Message, MessageLevel};

// Call Rust's mir_borrowck to check lifetimes of #[spec] and #[proof] code and variables
pub(crate) fn check<'tcx>(queries: &'tcx rustc_interface::Queries<'tcx>) {
    // fn bck_analysis<'tcx>(def_id: rustc_span::def_id::DefId, bck_results: &BorrowCheckResult<'tcx>) {
    //     dbg!(&def_id, &bck_results);
    // }

    queries.global_ctxt().expect("global_ctxt").enter(|tcx| {
        let hir = tcx.hir();
        let krate = hir.krate();
        for owner in &krate.owners {
            if let MaybeOwner::Owner(owner) = owner {
                match owner.node() {
                    OwnerNode::Item(item) => match &item.kind {
                        rustc_hir::ItemKind::Fn(..) => {
                            tcx.ensure().mir_borrowck(item.owner_id.def_id);
                            // tcx.enter(|tcx| {
                            //     let bck_results = tcx.mir_borrowck(item.owner_id.def_id);
                            //     bck_analysis(item.owner_id.def_id.to_def_id(), &bck_results);
                            // })
                        }
                        ItemKind::Impl(impll) => {
                            for item in impll.items {
                                match item.kind {
                                    AssocItemKind::Fn { .. } => {
                                        tcx.ensure().mir_borrowck(item.id.owner_id.def_id);
                                        // tcx.enter(|tcx| {
                                        //     let bck_results = tcx.mir_borrowck(item.id.owner_id.def_id);
                                        //     bck_analysis(item.id.owner_id.def_id.to_def_id(), &bck_results);
                                        // })
                                    }
                                    _ => {}
                                }
                            }
                        }
                        _ => {}
                    },
                    _ => (),
                }
            }
        }
    });
}

const PRELUDE: &str = "\
#![feature(box_patterns)]
#![allow(non_camel_case_types)]
#![allow(unused_imports)]
#![allow(unused_variables)]
#![allow(unused_assignments)]
#![allow(unreachable_patterns)]
#![allow(unused_parens)]
#![allow(unused_braces)]
#![allow(dead_code)]
#![allow(unreachable_code)]
#![allow(unconditional_recursion)]
#![allow(unused_mut)]
#![allow(unused_labels)]
use std::marker::PhantomData;
use std::rc::Rc;
use std::sync::Arc;
fn op<A, B>(a: A) -> B { panic!() }
fn static_ref<T>(t: T) -> &'static T { panic!() }
fn tracked_new<T>(t: T) -> Tracked<T> { panic!() }
fn tracked_exec_borrow<'a, T>(t: &'a T) -> &'a Tracked<T> { panic!() }
fn clone<T>(t: &T) -> T { panic!() }
fn rc_new<T>(t: T) -> std::rc::Rc<T> { panic!() }
fn arc_new<T>(t: T) -> std::sync::Arc<T> { panic!() }
fn box_new<T>(t: T) -> Box<T> { panic!() }
struct Tracked<A> { a: PhantomData<A> }
impl<A> Tracked<A> {
    pub fn get(self) -> A { panic!() }
    pub fn borrow(&self) -> &A { panic!() }
    pub fn borrow_mut(&mut self) -> &mut A { panic!() }
}
struct Ghost<A> { a: PhantomData<A> }
impl<A> Clone for Ghost<A> { fn clone(&self) -> Self { panic!() } }
impl<A> Copy for Ghost<A> { }
#[derive(Clone, Copy)] struct int;
#[derive(Clone, Copy)] struct nat;
struct FnSpec<Args, Output> { x: PhantomData<(Args, Output)> }
struct InvariantBlockGuard;
fn open_atomic_invariant_begin<'a, X, V>(_inv: &'a X) -> (&'a InvariantBlockGuard, V) { panic!(); }
fn open_local_invariant_begin<'a, X, V>(_inv: &'a X) -> (&'a InvariantBlockGuard, V) { panic!(); }
fn open_invariant_end<V>(_guard: &InvariantBlockGuard, _v: V) { panic!() }
fn index<'a, V, Idx, Output>(v: &'a V, index: Idx) -> &'a Output { panic!() }
";

fn emit_check_tracked_lifetimes<'tcx>(
    cmd_line_args: crate::config::Args,
    tcx: TyCtxt<'tcx>,
    verus_items: std::sync::Arc<VerusItems>,
    krate: &'tcx Crate<'tcx>,
    emit_state: &mut EmitState,
    erasure_hints: &ErasureHints,
) -> State {
    let gen_state = crate::lifetime_generate::gen_check_tracked_lifetimes(
        cmd_line_args,
        tcx,
        verus_items,
        krate,
        erasure_hints,
    );
    for line in PRELUDE.split('\n') {
        emit_state.writeln(line.replace("\r", ""));
    }

    for t in gen_state.trait_decls.iter() {
        emit_trait_decl(emit_state, t);
    }
    for d in gen_state.datatype_decls.iter() {
        emit_datatype_decl(emit_state, d);
    }
    for (a, fns) in gen_state.assoc_type_impls.iter() {
        emit_assoc_type_impl(emit_state, a, fns);
    }
    for f in gen_state.fun_decls.iter() {
        emit_fun_decl(emit_state, f);
    }
    gen_state
}

struct LifetimeCallbacks {}

impl rustc_driver::Callbacks for LifetimeCallbacks {
    // TODO(&mut)
    fn config(&mut self, config: &mut rustc_interface::Config) {
        config.override_queries = Some(|_session, providers, _| {
            providers.mir_promoted = |tcx, def_id| {
                let result = (rustc_interface::DEFAULT_QUERY_PROVIDERS.mir_promoted)(tcx, def_id);
                // dbg!(&def_id, &result.0.borrow());
                result
            };
        });
    }

    fn after_parsing<'tcx>(
        &mut self,
        _compiler: &rustc_interface::interface::Compiler,
        queries: &'tcx rustc_interface::Queries<'tcx>,
    ) -> rustc_driver::Compilation {
        check(queries);
        rustc_driver::Compilation::Stop
    }
}

struct LifetimeFileLoader {
    rust_code: String,
}

impl LifetimeFileLoader {
    const FILENAME: &'static str = "dummyrs.rs";
}

impl rustc_span::source_map::FileLoader for LifetimeFileLoader {
    fn file_exists(&self, _path: &std::path::Path) -> bool {
        panic!("unexpected call to file_exists")
    }

    fn read_file(&self, path: &std::path::Path) -> Result<String, std::io::Error> {
        assert!(path.display().to_string() == Self::FILENAME.to_string());
        Ok(self.rust_code.clone())
    }

    fn read_binary_file(&self, path: &std::path::Path) -> Result<Vec<u8>, std::io::Error> {
        assert!(path.display().to_string() == Self::FILENAME.to_string());
        Ok(self.rust_code.clone().into_bytes())
    }
}

#[derive(Debug, Deserialize)]
struct DiagnosticSpan {
    line_start: usize,
    line_end: usize,
    column_start: usize,
    column_end: usize,
}

#[derive(Debug, Deserialize)]
struct Diagnostic {
    message: String,
    level: String,
    spans: Vec<DiagnosticSpan>,
}

pub const LIFETIME_DRIVER_ARG: &'static str = "--internal-lifetime-driver";

pub fn lifetime_rustc_driver(rustc_args: &[String], rust_code: String) {
    let mut callbacks = LifetimeCallbacks {};
    let mut compiler = rustc_driver::RunCompiler::new(rustc_args, &mut callbacks);
    compiler.set_file_loader(Some(Box::new(LifetimeFileLoader { rust_code })));
    match compiler.run() {
        Ok(()) => (),
        Err(_) => std::process::exit(128),
    }
}

pub(crate) fn check_tracked_lifetimes<'tcx>(
    cmd_line_args: crate::config::Args,
    tcx: TyCtxt<'tcx>,
    verus_items: std::sync::Arc<VerusItems>,
    spans: &SpanContext,
    erasure_hints: &ErasureHints,
    lifetime_log_file: Option<File>,
) -> Result<Vec<Message>, VirErr> {
    let krate = tcx.hir().krate();
    let mut emit_state = EmitState::new();
    let gen_state = emit_check_tracked_lifetimes(
        cmd_line_args,
        tcx,
        verus_items,
        krate,
        &mut emit_state,
        erasure_hints,
    );
    let mut rust_code: String = String::new();
    for line in &emit_state.lines {
        rust_code.push_str(&line.text);
        rust_code.push('\n');
    }
    if let Some(mut file) = lifetime_log_file {
        write!(file, "{}", &rust_code).expect("error writing to lifetime log file");
    }
    let rustc_args = vec![LIFETIME_DRIVER_ARG, LifetimeFileLoader::FILENAME, "--error-format=json"];

    let mut child = std::process::Command::new(std::env::current_exe().unwrap())
        .args(&rustc_args[..])
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        // TODO(&mut)
        .stderr(std::process::Stdio::piped())
        .spawn()
        .expect("could not execute lifetime rustc process");
    let mut child_stdin = child.stdin.take().expect("take stdin");
    // std::fs::write("/tmp/verus_lifetime_generate.rs", rust_code.clone()).unwrap();
    child_stdin.write(rust_code.as_bytes()).expect("failed to send code to lifetime rustc");
    std::mem::drop(child_stdin);
    let run = child.wait_with_output().expect("lifetime rustc wait failed");
    let rust_output = std::str::from_utf8(&run.stderr[..]).unwrap().trim();
    let mut msgs: Vec<Message> = Vec::new();
    let debug = false;
    if rust_output.len() > 0 {
        for ss in rust_output.split("\n") {
            let diag: Diagnostic = serde_json::from_str(ss).expect("serde_json from_str");
            if diag.level == "failure-note" {
                continue;
            }
            if diag.level == "warning" {
                dbg!("internal error: unexpected warning");
                dbg!(diag);
                continue;
            }
            assert!(diag.level == "error");
            let msg_text = gen_state.unmangle_names(&diag.message);
            let mut msg = message_bare(MessageLevel::Error, &msg_text);
            if debug {
                dbg!(&msg);
            }
            for dspan in &diag.spans {
                if debug {
                    dbg!(&dspan);
                }
                let span = emit_state.get_span(
                    dspan.line_start - 1,
                    dspan.column_start - 1,
                    dspan.line_end - 1,
                    dspan.column_end - 1,
                );
                msg = msg.primary_span(&spans.to_air_span(span));
            }
            msgs.push(msg);
        }
    }
    if debug {
        dbg!(msgs.len());
    }
    if msgs.len() == 0 && !run.status.success() {
        Err(error("lifetime checking failed"))
    } else {
        Ok(msgs)
    }
}
