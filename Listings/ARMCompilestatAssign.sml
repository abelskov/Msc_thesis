(* --------- xi := const c ------------- *)
  RSSA.Assign (xi, NONE, NONE, SOME (RSSA.Var var_idx), NONE, NONE) =>
      [ ARM.MOV (showVarIdx xi, showVarIdx var_idx) ]

(* --------- xi := M[x]    ------------- *)
| RSSA.Assign (xi, NONE, NONE, SOME (RSSA.Array (var, var_idx)), NONE, NONE) =>
    let
      val m = symtabLookup (var, NONE) symtab
      val idx_reg_M = newName "idx"
      val addr_reg_M = newName "addr"
      val val_reg_M = newName "val"
      val xi_pp = showVarIdx xi
      val var_idx_pp = showVarIdx var_idx
    in
    (* extract M[x] to val_reg_M *)
    @ [ ARM.ROL (idx_reg_M, var_idx_pp, "3") ]
    @ [ ARM.ADD (addr_reg_M, m, idx_reg_M) ]
    @ [ ARM.LDR (val_reg_M, addr_reg_M, "0") ]
    (* move M[x] into xi *)
    @ [ ARM.MOV (xi_pp, val_reg_M) ]
    end

(* --------- xi := x --------------- *)
| RSSA.Assign (xi, SOME x, NONE, NONE, NONE, NONE) =>
      [ ARM.MOV (showVarIdx xi, showVarIdx x) ]

(* --------- xi := x uop r1 ------------ *)
| RSSA.Assign (xi, xOption, uopOption, r1Option, NONE, NONE) =>
    let
      val x = Option.getOpt(xOption, ("", NONE))
      val r1 = getLvalOption r1Option
      val uop = Option.valOf(uopOption)
      val xi_pp = showVarIdx xi
      val x_pp = showVarIdx x
    in
      [compileUop uop (xi_pp, x_pp, r1)]
    end

(* ---------- xi := x uop r1 binop r2 -------------- *)
| RSSA.Assign (xi, xOption, uopOption, r1Option, binopOption, r2Option) =>
    let
      val x = Option.getOpt(xOption, ("", NONE))
      val r1 = getLvalOption r1Option
      val r2 = getLvalOption r2Option
      val uop = Option.valOf(uopOption)
    in
      (compileBinop binopOption r1 r2)
    @ [compileUop uop (showVarIdx xi, showVarIdx x, r1)]
    end
