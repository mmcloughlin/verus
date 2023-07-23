use rustc_hir::definitions::DefPath;
use rustc_hir::{ItemKind, MaybeOwner, OwnerNode};
use rustc_middle::ty::{AdtDef, Ty, TyCtxt, TyKind};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use vir::ast::Ident;

// rustc uses u32 disambiguators to distinguish one DefPathData::Impl from another.
// However, these u32 values aren't necessarily stable between the erase_ghost and !erase_ghost
// versions of the HIR.
// Therefore, we replace these disambiguators with our own disambiguation based on the
// impl declaration.

type TypPath = Vec<String>;

// Represent as much of type structure as possible
// without including any impl names in any paths inside the type
#[derive(Debug, Serialize, Deserialize, Clone, PartialEq, Eq, Hash)]
pub(crate) enum TypTree {
    String(String),
    Path(TypPath),
    Decorate(String, Box<TypTree>),
    Apply(TypPath, Vec<Box<TypTree>>),
}

// A fingerprint for an impl block that captures everything we need
// to recognize the same impl block across ghost and erased compiler executions.
// Note that we don't care about distinguishing between multiple inherent (no trait) impl blocks
// with the same self type (e.g. impl S { fn f() {} } impl S { fn g() {} });
// these can just be merged into a single impl block.
// For impls for traits (e.g. impl T1 for S { ... } impl T2 for S { ... }),
// we should distinguish the impl blocks.
// Otherwise, we would lose precision by merging the blocks together,
// which would be sound but could cause our nontermination checking (recursion.rs)
// to report spurious errors.
#[derive(Debug, Serialize, Deserialize, Clone, PartialEq, Eq, Hash)]
struct ImplFingerprint {
    parent: TypPath,
    generics: Vec<String>,
    trait_path: Option<TypPath>,
    trait_args: Vec<TypTree>,
    self_typ: TypTree,
}

pub(crate) type ImplNameId = (TypPath, Vec<u32>);

#[derive(Debug, Serialize, Deserialize)]
pub(crate) struct ImplNameCtxt {
    pub(crate) impl_names: HashMap<ImplNameId, Ident>,
}

#[derive(Debug)]
pub(crate) struct ImplNameState {
    impl_table: HashMap<ImplFingerprint, Ident>,
}

fn def_path_to_impl_name_id<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_path: DefPath,
    num_segments: usize,
) -> ImplNameId {
    let mut path = vec![tcx.crate_name(def_path.krate).to_string()];
    let mut disambiguators: Vec<u32> = Vec::new();
    let mut i: usize = 0;
    for d in def_path.data.iter() {
        use rustc_hir::definitions::DefPathData;
        if i >= num_segments {
            break;
        }
        match &d.data {
            DefPathData::ValueNs(symbol) | DefPathData::TypeNs(symbol) => {
                path.push(symbol.to_string());
            }
            DefPathData::Ctor => {
                path.push(vir::def::RUST_DEF_CTOR.to_string());
            }
            DefPathData::Impl => {
                // We don't have names for the impls at this point, so just use "impl"
                path.push("impl".to_string());
                disambiguators.push(d.disambiguator);
            }
            _ => {}
        }
        i += 1;
    }
    (path, disambiguators)
}

fn def_path_to_path<'tcx>(tcx: TyCtxt<'tcx>, def_path: DefPath) -> TypPath {
    def_path_to_impl_name_id(tcx, def_path, usize::MAX).0
}

impl ImplNameCtxt {
    pub(crate) fn extend(&mut self, other: ImplNameCtxt) {
        for (id, x) in other.impl_names.into_iter() {
            if let Some(y) = self.impl_names.get(&id) {
                assert!(&x == y);
            } else {
                self.impl_names.insert(id, x);
            }
        }
    }

    pub(crate) fn get_impl_id<'tcx>(
        &self,
        tcx: TyCtxt<'tcx>,
        def_path: DefPath,
        num_segments: usize,
    ) -> Option<Ident> {
        let id = def_path_to_impl_name_id(tcx, def_path, num_segments);
        self.impl_names.get(&id).cloned()
    }
}

impl TypTree {
    fn short_name(&self) -> String {
        match self {
            TypTree::String(s) => s.clone(),
            TypTree::Path(p) | TypTree::Apply(p, _) => p.last().expect("path").clone(),
            TypTree::Decorate(_, t) => t.short_name(),
        }
    }
}

fn typ_tree<'tcx>(tcx: TyCtxt<'tcx>, ty: &Ty<'tcx>) -> TypTree {
    let box_rec = |ty: &Ty<'tcx>| -> Box<TypTree> { Box::new(typ_tree(tcx, ty)) };
    match ty.kind() {
        TyKind::Bool | TyKind::Char | TyKind::Uint(_) | TyKind::Int(_) | TyKind::Float(_) => {
            TypTree::String(ty.to_string())
        }
        TyKind::Adt(AdtDef(adt), args) => {
            let path = def_path_to_path(tcx, tcx.def_path(adt.did));
            let mut typ_args: Vec<Box<TypTree>> = Vec::new();
            for arg in args.iter() {
                match arg.unpack() {
                    rustc_middle::ty::subst::GenericArgKind::Type(t) => {
                        typ_args.push(box_rec(&t));
                    }
                    _ => {}
                }
            }
            TypTree::Apply(path, typ_args)
        }
        TyKind::Foreign(did) => TypTree::Path(def_path_to_path(tcx, tcx.def_path(*did))),
        TyKind::Str => TypTree::String("str".to_string()),
        TyKind::Array(t, _len) => TypTree::Decorate("array".to_string(), box_rec(t)),
        TyKind::Slice(t) => TypTree::Decorate("slice".to_string(), box_rec(t)),
        TyKind::RawPtr(tmut) => {
            TypTree::Decorate(format!("raw{:?}", tmut.mutbl), box_rec(&tmut.ty))
        }
        TyKind::Ref(_region, t, muta) => TypTree::Decorate(format!("ref{:?}", muta), box_rec(t)),
        TyKind::Never => TypTree::String("never".to_string()),
        TyKind::Tuple(ts) => {
            let path = vec!["tuple".to_string()];
            let typ_args = ts.iter().map(|t| box_rec(&t)).collect();
            TypTree::Apply(path, typ_args)
        }
        TyKind::Alias(_kind, alias) => {
            let path = def_path_to_path(tcx, tcx.def_path(alias.def_id));
            let mut typ_args: Vec<Box<TypTree>> = Vec::new();
            if let Some(args) = alias.substs.try_as_type_list() {
                for t in args.iter() {
                    typ_args.push(box_rec(&t));
                }
            }
            TypTree::Apply(path, typ_args)
        }
        TyKind::Param(_) => TypTree::String(ty.to_string()),
        TyKind::Bound(..) => TypTree::String(ty.to_string()),

        TyKind::FnDef(..) => TypTree::String("fndef".to_string()),
        TyKind::FnPtr(..) => TypTree::String("fnptr".to_string()),
        TyKind::Dynamic(..) => TypTree::String("dyn".to_string()),
        TyKind::Closure(..) => TypTree::String("closure".to_string()),
        TyKind::Generator(..) => TypTree::String("generator".to_string()),
        TyKind::GeneratorWitness(..) => TypTree::String("generator_witness".to_string()),

        TyKind::Placeholder(_) => panic!("unexpected placeholder type"),
        TyKind::Infer(_) => panic!("unexpected infer type"),
        TyKind::Error(_) => panic!("unexpected error type"),
    }
}

fn traverse_impls<'tcx>(
    tcx: TyCtxt<'tcx>,
    state: &mut ImplNameState,
    _export: bool,
) -> ImplNameCtxt {
    let hir = tcx.hir();
    let krate = hir.krate();
    let mut impl_names = HashMap::new();
    let mut make_name_table: HashMap<(TypPath, String, Option<String>), u64> = HashMap::new();
    let mut make_name =
        |parent: &TypPath, self_name: String, trait_name: Option<String>| -> Ident {
            let key = (parent.clone(), self_name.clone(), trait_name.clone());
            let n = if let Some(m) = make_name_table.get(&key) { m + 1 } else { 0 };
            make_name_table.insert(key, n);
            vir::def::impl_name(self_name, trait_name, n)
        };
    for owner in &krate.owners {
        if let MaybeOwner::Owner(owner) = owner {
            match owner.node() {
                OwnerNode::Item(item) => match &item.kind {
                    ItemKind::Impl(impll) => {
                        use crate::rustc_middle::ty::DefIdTree;
                        let impl_def_id = item.owner_id.to_def_id();
                        let impl_name_id =
                            def_path_to_impl_name_id(tcx, tcx.def_path(impl_def_id), usize::MAX);
                        let parent_id = tcx.parent(impl_def_id);
                        // compute ImplFingerprint fingerprint for impll
                        let parent_def_path = tcx.def_path(parent_id);
                        let parent = def_path_to_path(tcx, parent_def_path);
                        let mut generics = Vec::new();
                        for param in tcx.generics_of(impl_def_id).params.iter() {
                            generics.push(param.name.to_string());
                        }
                        let (trait_path, trait_args) = if let Some(tref) = &impll.of_trait {
                            let path = def_path_to_path(tcx, tcx.def_path(tref.path.res.def_id()));
                            let trait_ref =
                                tcx.impl_trait_ref(impl_def_id).expect("impl_trait_ref");
                            let mut trait_args: Vec<TypTree> = Vec::new();
                            for ty in trait_ref.0.substs.types() {
                                trait_args.push(typ_tree(tcx, &ty));
                            }
                            (Some(path), trait_args)
                        } else {
                            (None, vec![])
                        };
                        let trait_name =
                            trait_path.as_ref().map(|path| path.last().cloned().unwrap());
                        let self_typ = typ_tree(tcx, &tcx.type_of(impl_def_id));
                        let self_name = self_typ.short_name();
                        let fingerprint = ImplFingerprint {
                            parent: parent.clone(),
                            generics,
                            trait_path,
                            trait_args,
                            self_typ,
                        };
                        // store fingerprint and name in state
                        let prev = state.impl_table.get(&fingerprint);
                        let name = if let Some(name) = prev {
                            name.clone()
                        } else {
                            let name = make_name(&parent, self_name, trait_name);
                            state.impl_table.insert(fingerprint, name.clone());
                            name
                        };
                        assert!(!impl_names.contains_key(&impl_name_id));
                        impl_names.insert(impl_name_id, name);
                    }
                    _ => {}
                },
                _ => (),
            }
        }
    }
    ImplNameCtxt { impl_names }
}

pub(crate) fn collect_impls<'tcx>(tcx: TyCtxt<'tcx>) -> (ImplNameState, ImplNameCtxt) {
    let mut state = ImplNameState { impl_table: HashMap::new() };
    let impl_ctxt = traverse_impls(tcx, &mut state, false);
    (state, impl_ctxt)
}

pub(crate) fn export_impls<'tcx>(
    queries: &'tcx verus_rustc_interface::Queries<'tcx>,
    state: &mut ImplNameState,
) -> ImplNameCtxt {
    queries.global_ctxt().expect("global_ctxt").enter(|tcx| traverse_impls(tcx, state, false))
}
