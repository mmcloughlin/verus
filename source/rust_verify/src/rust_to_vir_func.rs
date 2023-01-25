use crate::attributes::{
    get_fuel, get_mode, get_publish, get_ret_mode, get_var_mode, get_verifier_attrs,
};
use crate::context::{BodyCtxt, Context};
use crate::rust_to_vir_base::{
    check_generics_bounds_fun, def_id_to_vir_path, foreign_param_to_var,
    maybe_mutref_mid_ty_to_vir, mid_ty_to_vir,
    is_tracked_or_ghost_type,
    local_to_var,
};
use crate::rust_to_vir_expr::{expr_to_vir_maybe_skip_prefix, pat_to_mut_var, ExprModifier};
use crate::util::{err_span_str, err_span_string, spanned_new, unsupported_err_span};
use crate::{unsupported, unsupported_err, unsupported_err_unless, unsupported_unless};
use rustc_ast::Attribute;
use rustc_hir::{
    def::Res, Body, BodyId, FnDecl, FnHeader, FnRetTy, FnSig, Generics, Param, PrimTy, QPath, Ty,
    TyKind, Unsafety,
};
use rustc_middle::ty::TyCtxt;
use rustc_span::symbol::{Ident, Symbol};
use rustc_span::Span;
use std::sync::Arc;
use vir::ast::{
    Fun, FunX, FunctionAttrsX, FunctionKind, FunctionX, GenericBoundX, KrateX, MaskSpec, Mode,
    ParamX, Typ, TypX, VirErr,
};
use vir::def::RETURN_VALUE;
use std::collections::HashMap;
use rustc_middle::ty::TyS;
use rustc_hir::{
    BindingAnnotation, Block, Expr, ExprKind, Local,
    Node, Pat, PatKind, Stmt, StmtKind,
    LocalSource, Path,
    PathSegment,
};

pub(crate) fn autospec_fun(path: &vir::ast::Path, method_name: String) -> vir::ast::Path {
    // turn a::b::c into a::b::method_name
    let mut pathx = (**path).clone();
    let mut segments = (*pathx.segments).clone();
    *segments.last_mut().expect("empty path") = Arc::new(method_name);
    pathx.segments = Arc::new(segments);
    Arc::new(pathx)
}

pub(crate) fn body_to_vir<'tcx>(
    ctxt: &Context<'tcx>,
    id: &BodyId,
    body: &Body<'tcx>,
    mode: Mode,
    external_body: bool,
    skip_stmts: Option<usize>,
) -> Result<vir::ast::Expr, VirErr> {
    let def = rustc_middle::ty::WithOptConstParam::unknown(id.hir_id.owner);
    let types = ctxt.tcx.typeck_opt_const_arg(def);
    let bctx = BodyCtxt { ctxt: ctxt.clone(), types, mode, external_body, in_ghost: mode != Mode::Exec };

    expr_to_vir_maybe_skip_prefix(&bctx, &body.value, ExprModifier::REGULAR, skip_stmts)
}

fn check_fn_decl<'tcx>(
    tcx: TyCtxt<'tcx>,
    decl: &'tcx FnDecl<'tcx>,
    attrs: &[Attribute],
    mode: Mode,
    output_ty: rustc_middle::ty::Ty<'tcx>,
) -> Result<Option<(Typ, Mode)>, VirErr> {
    let FnDecl { inputs: _, output, c_variadic, implicit_self } = decl;
    unsupported_unless!(!c_variadic, "c_variadic");
    match implicit_self {
        rustc_hir::ImplicitSelfKind::None => {}
        rustc_hir::ImplicitSelfKind::Imm => {}
        rustc_hir::ImplicitSelfKind::ImmRef => {}
        rustc_hir::ImplicitSelfKind::MutRef => {}
        _ => unsupported!("implicit_self"),
    }
    match output {
        rustc_hir::FnRetTy::DefaultReturn(_) => Ok(None),
        // REVIEW: there's no attribute syntax on return types,
        // so we always return the default mode.
        // The current workaround is to return a struct if the default doesn't work.
        rustc_hir::FnRetTy::Return(_ty) => {
            let typ = mid_ty_to_vir(tcx, output_ty, false);
            Ok(Some((typ, get_ret_mode(mode, attrs))))
        }
    }
}

fn find_body<'tcx>(ctxt: &Context<'tcx>, body_id: &BodyId) -> &'tcx Body<'tcx> {
    let owner = ctxt.krate.owners[body_id.hir_id.owner].as_ref();
    if let Some(owner) = owner {
        if let Some(body) = owner.nodes.bodies.get(&body_id.hir_id.local_id) {
            return body;
        }
    }
    panic!("Body not found");
}

fn check_new_strlit<'tcx>(ctx: &Context<'tcx>, sig: &'tcx FnSig<'tcx>) -> Result<(), VirErr> {
    let (decl, span) = match sig {
        FnSig { decl, span, .. } => (decl, span),
    };

    let sig_span = span;
    let expected_input_num = 1;

    if decl.inputs.len() != expected_input_num {
        return err_span_string(*sig_span, format!("Expected one argument to new_strlit"));
    }

    let (kind, span) = match &decl.inputs[0].kind {
        TyKind::Rptr(_, mutty) => (&mutty.ty.kind, mutty.ty.span),
        _ => return err_span_string(decl.inputs[0].span, format!("expected a str")),
    };

    let (res, span) = match kind {
        TyKind::Path(QPath::Resolved(_, path)) => (path.res, path.span),
        _ => return err_span_string(span, format!("expected str")),
    };

    if res != Res::PrimTy(PrimTy::Str) {
        return err_span_string(span, format!("expected a str"));
    }

    let (kind, span) = match decl.output {
        FnRetTy::Return(Ty { hir_id: _, kind, span }) => (kind, span),
        _ => return err_span_string(*sig_span, format!("expected a return type of StrSlice")),
    };

    let (res, span) = match kind {
        TyKind::Path(QPath::Resolved(_, path)) => (path.res, path.span),
        _ => return err_span_string(*span, format!("expected a StrSlice")),
    };

    let id = match res {
        Res::Def(_, id) => id,
        _ => return err_span_string(span, format!("")),
    };

    if !ctx.tcx.is_diagnostic_item(Symbol::intern("pervasive::string::StrSlice"), id) {
        return err_span_string(span, format!("expected a StrSlice"));
    }
    Ok(())
}

pub(crate) fn check_item_fn<'tcx>(
    ctxt: &Context<'tcx>,
    vir: &mut KrateX,
    id: rustc_span::def_id::DefId,
    kind: FunctionKind,
    visibility: vir::ast::Visibility,
    attrs: &[Attribute],
    sig: &'tcx FnSig<'tcx>,
    trait_path: Option<vir::ast::Path>,
    // (impl generics, impl def_id)
    self_generics: Option<(&'tcx Generics, rustc_span::def_id::DefId)>,
    generics: &'tcx Generics,
    body_id: &BodyId,
) -> Result<Option<Fun>, VirErr> {
    let path = def_id_to_vir_path(ctxt.tcx, id);
    let name = Arc::new(FunX { path: path.clone(), trait_path: trait_path.clone() });
    let is_new_strlit =
        ctxt.tcx.is_diagnostic_item(Symbol::intern("pervasive::string::new_strlit"), id);

    let mode = get_mode(Mode::Exec, attrs);

    let self_typ_params = if let Some((cg, impl_def_id)) = self_generics {
        Some(check_generics_bounds_fun(ctxt.tcx, cg, impl_def_id)?)
    } else {
        None
    };

    let fn_sig = ctxt.tcx.fn_sig(id);
    // REVIEW: rustc docs refer to skip_binder as "dangerous"
    let fn_sig = fn_sig.skip_binder();
    let inputs = fn_sig.inputs();

    let ret_typ_mode = match sig {
        FnSig {
            header: FnHeader { unsafety, constness: _, asyncness: _, abi: _ },
            decl,
            span: _,
        } => {
            unsupported_err_unless!(*unsafety == Unsafety::Normal, sig.span, "unsafe");
            check_fn_decl(ctxt.tcx, decl, attrs, mode, fn_sig.output())?
        }
    };
    let vattrs = get_verifier_attrs(attrs)?;

    if is_new_strlit {
        check_new_strlit(&ctxt, sig)?;
    }

    if is_new_strlit {
        let mut erasure_info = ctxt.erasure_info.borrow_mut();
        unsupported_err_unless!(
            vattrs.external_body,
            sig.span,
            "StrSlice::new must be external_body"
        );

        erasure_info.ignored_functions.push(sig.span.data());
        erasure_info.external_functions.push(name);
        return Ok(None);
    }

    if vattrs.external {
        let mut erasure_info = ctxt.erasure_info.borrow_mut();
        erasure_info.external_functions.push(name);
        return Ok(None);
    }

    let sig_typ_bounds = check_generics_bounds_fun(ctxt.tcx, generics, id)?;
    let fuel = get_fuel(&vattrs);

    let body = find_body(ctxt, body_id);
    let Body { params, value: _, generator_kind } = body;
    let mut vir_params: Vec<vir::ast::Param> = Vec::new();

    assert!(params.len() == inputs.len());
    for (param, input) in params.iter().zip(inputs.iter()) {
        let Param { hir_id, pat, ty_span: _, span } = param;

        // is_mut_var: means a parameter is like `mut x: X` (unsupported)
        // is_mut: means a parameter is like `x: &mut X`

        let (is_mut_var, name) = pat_to_mut_var(pat);
        if is_mut_var {
            return err_span_string(
                *span,
                format!(
                    "Verus does not support `mut` arguments (try writing `let mut param = param;` in the body of the function)"
                ),
            );
        }

        let name = Arc::new(name);
        let param_mode = get_var_mode(mode, ctxt.tcx.hir().attrs(*hir_id));

        let (is_mut, typ) = maybe_mutref_mid_ty_to_vir(ctxt.tcx, input);

        if is_mut && mode == Mode::Spec {
            return err_span_string(
                *span,
                format!("&mut argument not allowed for #[spec] functions"),
            );
        }

        let vir_param = spanned_new(*span, ParamX { name, typ, mode: param_mode, is_mut });
        vir_params.push(vir_param);
    }

    match generator_kind {
        None => {}
        _ => {
            unsupported_err!(sig.span, "generator_kind", generator_kind);
        }
    }

    let skip_stmts = if vattrs.uses_mode_param_uwrap_encoding {
        if mode != Mode::Exec {
            return err_span_str(
                sig.span,
                "'uses_mode_param_uwrap_encoding' is only for exec-mode functions",
            );
        }

        let n = handle_mode_wrapped_params(ctxt, body_id, &sig.span, body, &mut vir_params, inputs);
        Some(n)
    } else {
        None
    };

    let mut vir_body = body_to_vir(ctxt, body_id, body, mode, vattrs.external_body, skip_stmts)?;

    let header = vir::headers::read_header(&mut vir_body)?;
    match (&kind, header.no_method_body) {
        (FunctionKind::TraitMethodDecl { .. }, true) => {}
        (FunctionKind::TraitMethodDecl { .. }, false) => {
            return err_span_str(
                sig.span,
                "trait method declaration body must end with call to no_method_body()",
            );
        }
        (_, false) => {}
        (_, true) => {
            return err_span_str(
                sig.span,
                "no_method_body can only appear in trait method declarations",
            );
        }
    }
    if mode == Mode::Spec && (header.require.len() + header.ensure.len()) > 0 {
        return err_span_str(sig.span, "spec functions cannot have requires/ensures");
    }
    if mode != Mode::Spec && header.recommend.len() > 0 {
        return err_span_str(sig.span, "non-spec functions cannot have recommends");
    }
    if header.ensure.len() > 0 {
        match (&header.ensure_id_typ, ret_typ_mode.as_ref()) {
            (None, None) => {}
            (None, Some(_)) => {
                return err_span_str(sig.span, "ensures clause must be a closure");
            }
            (Some(_), None) => {
                return err_span_str(sig.span, "ensures clause cannot be a closure");
            }
            (Some((_, typ)), Some((ret_typ, _))) => {
                if !vir::ast_util::types_equal(&typ, &ret_typ) {
                    return err_span_string(
                        sig.span,
                        format!(
                            "return type is {:?}, but ensures expects type {:?}",
                            &ret_typ, &typ
                        ),
                    );
                }
            }
        }
    }
    let params = Arc::new(vir_params);
    let (ret_name, ret_typ, ret_mode) = match (header.ensure_id_typ, ret_typ_mode) {
        (None, None) => {
            (Arc::new(RETURN_VALUE.to_string()), Arc::new(TypX::Tuple(Arc::new(vec![]))), mode)
        }
        (None, Some((typ, mode))) => (Arc::new(RETURN_VALUE.to_string()), typ, mode),
        (Some((x, _)), Some((typ, mode))) => (x, typ, mode),
        _ => panic!("internal error: ret_typ"),
    };
    let ret = spanned_new(
        sig.span,
        ParamX { name: ret_name, typ: ret_typ, mode: ret_mode, is_mut: false },
    );
    let typ_bounds = {
        let mut typ_bounds: Vec<(vir::ast::Ident, vir::ast::GenericBound)> = Vec::new();
        if let FunctionKind::TraitMethodDecl { .. } = kind {
            let bound = GenericBoundX::Traits(vec![]);
            typ_bounds.push((vir::def::trait_self_type_param(), Arc::new(bound)));
        }
        if let Some(self_typ_params) = self_typ_params {
            typ_bounds.append(&mut (*self_typ_params).clone());
        }
        typ_bounds.extend_from_slice(&sig_typ_bounds[..]);
        Arc::new(typ_bounds)
    };
    let publish = get_publish(&vattrs);
    let autospec = vattrs.autospec.map(|method_name| {
        let path = autospec_fun(&path, method_name.clone());
        Arc::new(FunX { path, trait_path: trait_path.clone() })
    });

    if vattrs.nonlinear && vattrs.spinoff_prover {
        return err_span_str(
            sig.span,
            "#[verifier(spinoff_prover)] is implied for assert by nonlinear_arith",
        );
    }
    let fattrs = FunctionAttrsX {
        uses_ghost_blocks: vattrs.verus_macro,
        inline: vattrs.inline,
        hidden: Arc::new(header.hidden),
        custom_req_err: vattrs.custom_req_err,
        no_auto_trigger: vattrs.no_auto_trigger,
        broadcast_forall: vattrs.broadcast_forall,
        bit_vector: vattrs.bit_vector,
        autoview: vattrs.autoview,
        autospec,
        atomic: vattrs.atomic,
        integer_ring: vattrs.integer_ring,
        is_decrease_by: vattrs.decreases_by,
        check_recommends: vattrs.check_recommends,
        nonlinear: vattrs.nonlinear,
        spinoff_prover: vattrs.spinoff_prover,
        memoize: vattrs.memoize,
    };

    let mut recommend: Vec<vir::ast::Expr> = (*header.recommend).clone();
    if let Some(decrease_when) = &header.decrease_when {
        // Automatically add decrease_when to recommends
        recommend.push(decrease_when.clone());
    }

    // This function is marked 'private' at the source level to prevent the user from
    // calling it. But we translate things to point to it internally, so we need to
    // mark it non-private in order to avoid errors down the line.
    let mut visibility = visibility;
    if path == vir::def::exec_nonstatic_call_path() {
        visibility.is_private = false;
    }

    let func = FunctionX {
        name: name.clone(),
        kind,
        visibility,
        mode,
        fuel,
        typ_bounds,
        params,
        ret,
        require: if mode == Mode::Spec { Arc::new(recommend) } else { header.require },
        ensure: header.ensure,
        decrease: header.decrease,
        decrease_when: header.decrease_when,
        decrease_by: header.decrease_by,
        broadcast_forall: None,
        mask_spec: header.invariant_mask,
        is_const: false,
        publish,
        attrs: Arc::new(fattrs),
        body: if vattrs.external_body || header.no_method_body { None } else { Some(vir_body) },
        extra_dependencies: header.extra_dependencies,
    };

    let function = spanned_new(sig.span, func);
    vir.functions.push(function);
    Ok(Some(name))
}

pub(crate) fn check_item_const<'tcx>(
    ctxt: &Context<'tcx>,
    vir: &mut KrateX,
    span: Span,
    id: rustc_span::def_id::DefId,
    visibility: vir::ast::Visibility,
    attrs: &[Attribute],
    typ: &Typ,
    body_id: &BodyId,
) -> Result<(), VirErr> {
    let path = def_id_to_vir_path(ctxt.tcx, id);
    let name = Arc::new(FunX { path, trait_path: None });
    let mode = get_mode(Mode::Exec, attrs);
    let vattrs = get_verifier_attrs(attrs)?;
    let fuel = get_fuel(&vattrs);
    if vattrs.external {
        let mut erasure_info = ctxt.erasure_info.borrow_mut();
        erasure_info.external_functions.push(name);
        return Ok(());
    }
    let body = find_body(ctxt, body_id);
    let vir_body = body_to_vir(ctxt, body_id, body, mode, vattrs.external_body, None)?;

    let ret_name = Arc::new(RETURN_VALUE.to_string());
    let ret = spanned_new(span, ParamX { name: ret_name, typ: typ.clone(), mode, is_mut: false });
    let func = FunctionX {
        name,
        kind: FunctionKind::Static,
        visibility,
        mode: Mode::Spec, // the function has mode spec; the mode attribute goes into ret.x.mode
        fuel,
        typ_bounds: Arc::new(vec![]),
        params: Arc::new(vec![]),
        ret,
        require: Arc::new(vec![]),
        ensure: Arc::new(vec![]),
        decrease: Arc::new(vec![]),
        decrease_when: None,
        decrease_by: None,
        broadcast_forall: None,
        mask_spec: MaskSpec::NoSpec,
        is_const: true,
        publish: get_publish(&vattrs),
        attrs: Default::default(),
        body: if vattrs.external_body { None } else { Some(vir_body) },
        extra_dependencies: vec![],
    };
    let function = spanned_new(span, func);
    vir.functions.push(function);
    Ok(())
}

pub(crate) fn check_foreign_item_fn<'tcx>(
    ctxt: &Context<'tcx>,
    vir: &mut KrateX,
    id: rustc_span::def_id::DefId,
    span: Span,
    visibility: vir::ast::Visibility,
    attrs: &[Attribute],
    decl: &'tcx FnDecl<'tcx>,
    idents: &[Ident],
    generics: &'tcx Generics,
) -> Result<(), VirErr> {
    let mode = get_mode(Mode::Exec, attrs);

    let fn_sig = ctxt.tcx.fn_sig(id);
    // REVIEW: rustc docs refer to skip_binder as "dangerous"
    let fn_sig = fn_sig.skip_binder();
    let inputs = fn_sig.inputs();

    let ret_typ_mode = check_fn_decl(ctxt.tcx, decl, attrs, mode, fn_sig.output())?;
    let typ_bounds = check_generics_bounds_fun(ctxt.tcx, generics, id)?;
    let vattrs = get_verifier_attrs(attrs)?;
    let fuel = get_fuel(&vattrs);
    let mut vir_params: Vec<vir::ast::Param> = Vec::new();

    assert!(idents.len() == inputs.len());
    for (param, input) in idents.iter().zip(inputs.iter()) {
        let name = Arc::new(foreign_param_to_var(param));

        let (is_mut, typ) = maybe_mutref_mid_ty_to_vir(ctxt.tcx, input);

        // REVIEW: the parameters don't have attributes, so we use the overall mode
        let vir_param = spanned_new(param.span, ParamX { name, typ, mode, is_mut });
        vir_params.push(vir_param);
    }
    let path = def_id_to_vir_path(ctxt.tcx, id);
    let name = Arc::new(FunX { path, trait_path: None });
    let params = Arc::new(vir_params);
    let (ret_typ, ret_mode) = match ret_typ_mode {
        None => (Arc::new(TypX::Tuple(Arc::new(vec![]))), mode),
        Some((typ, mode)) => (typ, mode),
    };
    let ret_param = ParamX {
        name: Arc::new(RETURN_VALUE.to_string()),
        typ: ret_typ,
        mode: ret_mode,
        is_mut: false,
    };
    let ret = spanned_new(span, ret_param);
    let func = FunctionX {
        name,
        kind: FunctionKind::Static,
        visibility,
        fuel,
        mode,
        typ_bounds,
        params,
        ret,
        require: Arc::new(vec![]),
        ensure: Arc::new(vec![]),
        decrease: Arc::new(vec![]),
        decrease_when: None,
        decrease_by: None,
        broadcast_forall: None,
        mask_spec: MaskSpec::NoSpec,
        is_const: false,
        publish: None,
        attrs: Default::default(),
        body: None,
        extra_dependencies: vec![],
    };
    let function = spanned_new(span, func);
    vir.functions.push(function);
    Ok(())
}


/*fn handle_mode_wrapped_params<'tcx>(
    ctxt: &Context<'tcx>,
    span: &Span,
    vir_body: &mut Expr,
    vir_params: Vec<vir::ast::Param>,
    inputs: &[&'tcx TyS<'tcx>]) -> Result<Vec<vir::ast::Param>, ()>
{
    let (vir_body_stmts, vir_body_expr) = match &vir_body.x {
        ExprX::Block(stmts, expr) => (stmts, expr),
        _ => { return Err(()); }
    };

    let mut expected_params_to_map = vec![];
    assert!(vir_params.len() == inputs.len());
    for (vir_param, input) in vir_params.iter().zip(inputs.iter()) {
        if is_tracked_or_ghost_type(ctxt.tcx, input) {
            expected_params_to_map.push(vir_param.x.name.clone());
        }
    }

    if vir_body_stmts.len() < expected_params_to_map.len() + 1 {
        return Err(());
    }

    let mut new_names = vec![];
    for i in 0..expected_params_to_map.len() {
        match &vir_body_stmts[i].x {
            StmtX::Decl { pattern, mode: Mode::Exec, init: None } => {
                match &pattern.x {
                    PatternX::Var { name, mutable: false } => {
                        new_names.push(name.clone());
                    }
                    _ => {
                        return Err(());
                    }
                }
            }
            _ => {
                return Err(());
            }
        }
    }

    let mut name_map: HashMap<vir::ast::Ident, vir::ast::Ident> = HashMap::new();
    let mut lhss: Vec<vir::ast::Ident> = vec![];
    let mut rhss: Vec<vir::ast::Ident> = vec![];

    let lhs_to_ident = |lhs: &Expr| {
        match &lhs.x {
            ExprX::Loc(e) => {
                match &e.x {
                    ExprX::VarLoc(ident) => Ok(ident.clone()),
                    _ => Err(()),
                }
            }
            _ => Err(()),
        }
    };
    let rhs_to_ident = |rhs: &Expr| {
        match &rhs.x {
            ExprX::Var(ident) => Ok(ident.clone()),
            _ => Err(()),
        }
    };

    match &vir_body_stmts[expected_params_to_map.len()].x {
        StmtX::Expr(e_ghost_block) => {
            match &e_ghost_block.x {
                ExprX::Ghost { alloc_wrapper: None, tracked: false, expr } => {
                    match &expr.x {
                        ExprX::Block(block_stmts, None) => {
                            if block_stmts.len() != expected_params_to_map.len() {
                                return Err(());
                            }
                            for stmt in block_stmts.iter() {
                                match &stmt.x {
                                    StmtX::Expr(assign_expr) => {
                                        match &assign_expr.x {
                                            ExprX::Assign { init_not_mut: true, lhs, rhs } => {
                                                let lhs_ident = lhs_to_ident(lhs)?;
                                                let rhs_ident = rhs_to_ident(rhs)?;
                                                lhss.push(lhs_ident.clone());
                                                rhss.push(rhs_ident.clone());
                                                name_map.insert(rhs_ident, lhs_ident);
                                            }
                                            _ => { return Err(()); }
                                        }
                                    }
                                    _ => { return Err(()); }
                                }
                            }
                        }
                        _ => { return Err(()); }
                    }
                }
                _ => { return Err(()); }
            }
        }
        _ => { return Err(()); }
    }

    expected_params_to_map.sort();
    new_names.sort();
    lhss.sort();
    rhss.sort();

    let idents_unique = |v: &Vec<vir::ast::Ident>| {
        if v.len() >= 2 {
            // Can assume sorted
            for i in 0 .. v.len() - 1 {
                if v[i] == v[i + 1] {
                    return false;
                }
            }
        }
        true
    };

    if !idents_unique(&expected_params_to_map) {
        return Err(());
    }
    if !idents_unique(&new_names) {
        return Err(());
    }
    if expected_params_to_map != rhss {
        return Err(());
    }
    if new_names != lhss {
        return Err(());
    }
    
    let mut vir_params = vir_params;
    for vir_param in vir_params.iter_mut() {
        match name_map.get(&vir_param.x.name) {
            None => { }
            Some(new_name) => {
                *vir_param = spanned_new(*span, ParamX {
                        name: new_name.clone(), ..vir_param.x.clone() })
            }
        }
    }

    let vir_body_stmts = Arc::new(vir_body_stmts[ expected_params_to_map.len() + 1 .. ].to_vec());
    *vir_body = vir_body.new_x(ExprX::Block(vir_body_stmts, vir_body_expr.clone()));

    Ok(vir_params)
}*/

fn handle_mode_wrapped_params<'tcx>(
    ctxt: &Context<'tcx>,
    body_id: &BodyId,
    span: &Span,
    body: &Body<'tcx>,
    vir_params: &mut Vec<vir::ast::Param>,
    inputs: &[&'tcx TyS<'tcx>]) -> usize
{
    let def = rustc_middle::ty::WithOptConstParam::unknown(body_id.hir_id.owner);
    let types = ctxt.tcx.typeck_opt_const_arg(def);

    let stmts = match &body.value.kind {
        ExprKind::Block(block, _) => {
            block.stmts
        },
        _ => { panic!("expected block"); }
    };

    let mut tracked_params: Vec<String> = vec![];
    let mut ghost_params: Vec<String> = vec![];

    assert!(vir_params.len() == inputs.len());
    for (vir_param, input) in vir_params.iter().zip(inputs.iter()) {
        match is_tracked_or_ghost_type(ctxt.tcx, input) {
            Some(true) => 
                tracked_params.push((*vir_param.x.name).clone()),
            Some(false) =>
                ghost_params.push((*vir_param.x.name).clone()),
            None => { }
        }
    }

    let n_stmts = tracked_params.len() + ghost_params.len() + 2;
    assert!(stmts.len() >= n_stmts);
    let ghost_let_stmts = &stmts[0 .. ghost_params.len()];
    let ghost_assign_block = &stmts[ghost_params.len()];
    let tracked_let_stmts = &stmts[ghost_params.len() + 1 .. ghost_params.len() + 1 + tracked_params.len()];
    let tracked_assign_block = &stmts[ghost_params.len() + 1 + tracked_params.len()];

    let decl_to_name = |stmt: &Stmt| {
        match &stmt.kind {
            StmtKind::Local(Local { pat: Pat { kind: PatKind::Binding(
                BindingAnnotation::Unannotated,
                hir_id,
                ident,
                None
            ), .. },
            ty: _,
            init: None,
            hir_id: _,
            span: _,
            source: LocalSource::Normal,
            }) => local_to_var(ident, hir_id.local_id),
            _ => panic!("expected 'let' statement here"),
        }
    };

    let expr_to_var_name = |expr: &Expr| {
        match &expr.kind {
            ExprKind::Path(QPath::Resolved(None, Path { res: Res::Local(id), segments, span: _ })) if segments.len() == 1 => {
                match &segments[0] {
                    PathSegment { ident: _, hir_id: _, res: Some(_), args: None, infer_args: true } => { }
                    _ => panic!("expected call"),
                }
                match ctxt.tcx.hir().get(*id) {
                    Node::Binding(pat) => {
                        crate::rust_to_vir_expr::pat_to_var(pat)
                    }
                    _ => panic!("expected var"),
                }
            }
            _ => panic!("expected var"),
        }
    };

    let expr_get_call_to_var_name = |expr: &Expr, tracked: bool| {
        match &expr.kind {
            ExprKind::MethodCall(_name_and_generics, _call_span_0, all_args, _fn_span) => {
                assert!(all_args.len() == 1);
                let fn_def_id = types
                    .type_dependent_def_id(expr.hir_id)
                    .expect("def id of the method definition");
                let f_name = ctxt.tcx.def_path_str(fn_def_id);
                assert!(f_name == (if tracked {
                    "builtin::Tracked::<A>::get"
                } else {
                    "builtin::Ghost::<A>::get"
                }));
                expr_to_var_name(&all_args[0])
            }
            _ => panic!("expected call"),
        }
    };

    let assign_to_name_pair = |stmt: &Stmt, tracked: bool| {
        match &stmt.kind {
            StmtKind::Semi(Expr {
                kind: ExprKind::Assign(lhs, rhs, _span),
                ..
            }) => {
                let lhs_name = expr_to_var_name(lhs);
                let rhs_name = expr_get_call_to_var_name(rhs, tracked);
                (lhs_name, rhs_name)
            }
            _ => panic!("expected assignment"),
        }
    };

    let block_to_stmts = |stmt: &'tcx Stmt| {
        match &stmt.kind {
            StmtKind::Expr(Expr {
                kind: ExprKind::Block(Block { stmts, expr: None, .. }, _),
                ..
            }) => stmts,
            _ => panic!("expected 'block' expr here"),
        }
    };

    let ghost_new_names: Vec<String> = ghost_let_stmts.iter().map(|stmt|
        decl_to_name(stmt)
    ).collect();
    let tracked_new_names: Vec<String> = tracked_let_stmts.iter().map(|stmt|
        decl_to_name(stmt)
    ).collect();

    let ghost_assign_stmts: &[Stmt<'tcx>] = block_to_stmts(ghost_assign_block);
    let tracked_assign_stmts: &[Stmt<'tcx>] = block_to_stmts(tracked_assign_block);

    assert!(ghost_assign_stmts.len() == ghost_params.len());
    assert!(tracked_assign_stmts.len() == tracked_params.len());

    let ghost_assign_pairs: Vec<(String, String)> = ghost_assign_stmts.iter().map(|stmt|
        assign_to_name_pair(stmt, false)
    ).collect();
    let tracked_assign_pairs: Vec<(String, String)> = tracked_assign_stmts.iter().map(|stmt|
        assign_to_name_pair(stmt, true)
    ).collect();

    for i in 0 .. ghost_assign_pairs.len() {
        assert!(ghost_assign_pairs[i].0 == ghost_new_names[i]);
        assert!(ghost_assign_pairs[i].1 == ghost_params[i]);
    }
    for i in 0 .. tracked_assign_pairs.len() {
        assert!(tracked_assign_pairs[i].0 == tracked_new_names[i]);
        assert!(tracked_assign_pairs[i].1 == tracked_params[i]);
    }

    let mut name_map: HashMap<String, String> = HashMap::new();
    for pair in ghost_assign_pairs.into_iter().chain(tracked_assign_pairs.into_iter()) {
        name_map.insert(pair.1, pair.0);
    }

    for vir_param in vir_params.iter_mut() {
        match name_map.get(&*vir_param.x.name) {
            None => { }
            Some(new_name) => {
                *vir_param = spanned_new(*span, ParamX {
                        name: Arc::new(new_name.clone()), ..vir_param.x.clone() })
            }
        }
    }

    n_stmts
}

