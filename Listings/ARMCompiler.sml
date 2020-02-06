structure ARMCompiler :> ARMCompiler = struct

  exception Error of string*(int*int)


  (* Name generator for labels and temporary symbolic registers *)
  val counter = ref 0

  fun newName reg_name =
      let val () = counter := !counter + 1
          val n = Int.toString (!counter)
      in
        "_" ^ reg_name ^ "_" ^ n ^ "_"
      end

  (* I've dedicated x28 as my heap pointer *)
  val HP = "x28"
  (* frame pointer *)
  val FP = "x29"
  (* link register *)
  val LR = "x30"
  (* stack pointer *)
  val SP = "sp"

  fun concatWith [] s = ""
    | concatWith [x] s = x
    | concatWith (x :: xs) s = x ^ s ^ concatWith xs s

  fun concatMap f xs = List.concat (List.map f xs)

  fun showVarIdx (x, SOME idx) = x ^ "_" ^ Int.toString(idx)
    | showVarIdx (x, NONE) = x
  
  fun showArr arr var_idx = arr ^ "[" ^ showVarIdx var_idx ^ "]"

  fun showUop uop =
    case uop of
      RSSA.Add =>     " += "
    | RSSA.Sub =>     " -= "
    | RSSA.XorWith => " ^= "
    | RSSA.RoL =>     " <<= "
    | RSSA.RoR =>     " >>= "

  fun showBinop binop = 
    case binop of
      RSSA.Plus =>    " + "
    | RSSA.Minus =>   " - "
    | RSSA.Times =>   " * "
    | RSSA.Divide =>  " / "
    | RSSA.Modulo =>  " % "
    | RSSA.Xor =>     " ^ "
    | RSSA.BAnd =>    " & "
    | RSSA.BOr =>     " | "
    | RSSA.ShiftL =>  " << "
    | RSSA.ShiftR =>  " >> "
    | RSSA.Equal =>   " == "
    | RSSA.Neq =>     " != "
    | RSSA.Less =>    " < "
    | RSSA.Greater => " > "
    | RSSA.Leq =>     " <= "
    | RSSA.Geq =>     " >= "


  fun compileUop uop =
    case uop of
      RSSA.Add =>     ARM.ADD
    | RSSA.Sub =>     ARM.SUB
    | RSSA.XorWith => ARM.EOR
    | RSSA.RoL =>     ARM.ROL
    | RSSA.RoR =>     ARM.ROR

  fun compileBinop NONE r1 r2 = []
    | compileBinop (SOME binop) r1 r2 =
    case binop of
      RSSA.Plus => [ ARM.ADD (r1, r1, r2) ]
    | RSSA.Minus => [ ARM.SUB(r1, r1, r2) ]
    | RSSA.Times => [ ARM.MUL (r1, r1, r2) ]
    | RSSA.Divide => [ ARM.SDIV (r1, r1, r2) ]
    | RSSA.Modulo => let val tmp_reg = newName "tmp"
                     in
                       [ ARM.SDIV (tmp_reg, r1, r2) ] @
                       [ ARM.MUL (tmp_reg, tmp_reg, r2) ] @
                       [ ARM.SUB (r1, r1, tmp_reg) ]
                     end
    | RSSA.Xor => [ ARM.EOR (r1, r1, r2) ]
    | RSSA.BAnd => [ ARM.AND (r1, r1, r2) ]
    | RSSA.BOr =>  [ ARM.ORR (r1, r1, r2) ]
    | RSSA.ShiftL => [ ARM.ROL(r1, r1, r2) ]
    | RSSA.ShiftR => [ ARM.ROR (r1, r1, r2) ]
    | _ => raise Fail "this should never happen in compileBinop"


    (* arrayalloc (size, place) generates code for allocating arrays on stack
       by decrementing the stack pointer by a number of words.
       The arguments for this function are as follows:
         size: contains the logical array size (number of array elements)
         place: will contain the address of new allocation (old HP)
     *)
  fun arrayalloc (size, place) =
    let val siz = Option.valOf(Int.fromString(size))
    in
      [ ARM.SUB (SP, SP, Int.toString(siz * 8)) ] @
      [ ARM.MOV (place, SP) ]
    end

  fun getLvalOption NONE = ""
    | getLvalOption (SOME (RSSA.Var (var_idx))) = showVarIdx var_idx
    | getLvalOption (SOME (RSSA.Array (var, var_idx))) = raise Fail "lVal on the right of expression is an array (should have been a var)"

  fun symtabLookup x symtab = if Option.isSome (SymTab.lookup x symtab)
                              then Option.valOf (SymTab.lookup x symtab)
                              else raise Fail "lookup in symtab didnt find anything"

  fun compileStat symtab s =
    case s of
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
      val arr_pp = showArr var var_idx
    in
      [ ARM.COMMENT (xi_pp ^ " := " ^ arr_pp) ]
    (* extract M[x] to val_reg_M *)
   @  [ ARM.ROL (idx_reg_M, var_idx_pp, "3") ]
   @  [ ARM.ADD (addr_reg_M, m, idx_reg_M) ]
   @  [ ARM.LDR (val_reg_M, addr_reg_M, "0") ]
    (* move M[x] into xi *)
   @  [ ARM.MOV (xi_pp, val_reg_M) ]
    end

    (* --------- xi := x --------------- *)
    | RSSA.Assign (xi, SOME x, NONE, NONE, NONE, NONE) =>
      [ ARM.COMMENT (showVarIdx xi ^ " := " ^ showVarIdx x)] @
      [ ARM.MOV (showVarIdx xi, showVarIdx x) ]

    (* --------- xi := x uop r1 ------------ *)
    | RSSA.Assign (xi, xOption, uopOption, r1Option, NONE, NONE) =>
    let
      val x = Option.getOpt(xOption, ("", NONE))
      val r1 = getLvalOption r1Option
      val uop = Option.valOf(uopOption)
      val xi_pp = showVarIdx xi
      val x_pp = showVarIdx x
      val uopCode = [compileUop uop (xi_pp, x_pp, r1)]
      val uop_pp = showUop uop
    in
      [ ARM.COMMENT (xi_pp ^ uop_pp ^ r1) ] @
      uopCode
    end

    (* ---------- xi := x uop r1 binop r2 -------------- *)
    | RSSA.Assign (xi, xOption, uopOption, r1Option, binopOption, r2Option) =>
    let
      val x = Option.getOpt(xOption, ("", NONE))
      val r1 = getLvalOption r1Option
      val r2 = getLvalOption r2Option
      val uop = Option.valOf(uopOption)
      val binop = Option.valOf(binopOption)
      val uopCode = [compileUop uop (showVarIdx xi, showVarIdx x, r1)]
      val binopCode = compileBinop binopOption r1 r2
      val xi_pp = showVarIdx xi
      val uop_pp = showUop uop
      val binop_pp = showBinop binop
    in
      [ ARM.COMMENT (xi_pp ^ uop_pp ^ r1 ^ binop_pp ^ r2) ] @
      binopCode @
      uopCode
    end

    | RSSA.MemUpdate (arrM, x, uop, r1, NONE, NONE) =>
        let val m = symtabLookup (arrM, NONE) symtab
            val idx_reg_M = newName "idx"
            val addr_reg_M = newName "addr"
            val val_reg_M = newName "val"
            val r1_i = getLvalOption (SOME r1)
            val uopCode = [ compileUop uop (val_reg_M, val_reg_M, r1_i) ] 
        in
          (* M[xi] uop= r1 *)
          [ ARM.COMMENT (showArr arrM x ^ showUop uop ^ r1_i) ] @
          (* extract M[x] to val_reg_M *)
          [ ARM.ROL (idx_reg_M, showVarIdx x, "3") ] @
          [ ARM.ADD (addr_reg_M, m, idx_reg_M) ] @
          [ ARM.LDR (val_reg_M, addr_reg_M, "0") ] @
          uopCode @
          [ ARM.STR (val_reg_M, addr_reg_M, "0") ]
        end

        (* No RSSACompiler case results in this *)
    | RSSA.MemUpdate (_, _, _, _, _, _) =>
        raise Fail "MemUpdate like this is not currently implemented"

    | RSSA.AssignSwap (xi, yj, y, x) => 
        (* xi, yj := y, x *)
        [ ARM.COMMENT (showVarIdx xi ^ ", " ^ showVarIdx yj ^ " := " ^
                       showVarIdx y ^ ", " ^ showVarIdx x) ] @
        [ ARM.MOV (showVarIdx xi, showVarIdx y) ] @
        [ ARM.MOV (showVarIdx yj, showVarIdx x) ]

    | RSSA.MemSwap (arrM, x, arrN, y) =>
        let val m = symtabLookup (arrM, NONE) symtab
            val n = symtabLookup (arrN, NONE) symtab
            val idx_reg_M = newName "idx"
            val idx_reg_N = newName "idx"
            val addr_reg_M = newName "addr"
            val addr_reg_N = newName "addr"
            val val_reg_M = newName "val"
            val val_reg_N = newName "val"
        in
          (* M[x] <-> N[y]; *)
          [ ARM.COMMENT (showArr arrM x ^ " <-> " ^ showArr arrN y)  ] @
          (* extract M[x] to val_reg_M *)
          [ ARM.ROL (idx_reg_M, showVarIdx x, "3") ] @
          [ ARM.ADD (addr_reg_M, m, idx_reg_M) ] @
          [ ARM.LDR (val_reg_M, addr_reg_M, "0") ] @
          (* extract N[y] to val_reg_N *)
          [ ARM.ROL (idx_reg_N, showVarIdx y, "3") ] @
          [ ARM.ADD (addr_reg_N, n, idx_reg_N) ] @
          [ ARM.LDR (val_reg_N, addr_reg_N, "0") ] @
          (* store N[y] in M[x] *)
          [ ARM.STR (val_reg_N, addr_reg_M, "0") ] @
          (* store M[x] in N[y] *)
          [ ARM.STR (val_reg_M, addr_reg_N, "0") ]
        end

    | RSSA.VarMemSwap (xii, arrM, yj, xi) =>
        let val m = symtabLookup (arrM, NONE) symtab
            val idx_reg_M = newName "idx"
            val addr_reg_M = newName "addr"
            val val_reg_M = newName "val"
        in
          (* M[y] <-> x; *)
          [ ARM.COMMENT (showArr arrM yj ^ " <-> " ^ showVarIdx xi) ] @
          (* yj * 8 is the index we want to use *)
          [ ARM.ROL (idx_reg_M, showVarIdx yj, "3") ] @
          (* swap_reg has the address of M[yj] *)
          [ ARM.ADD (addr_reg_M, m, idx_reg_M) ] @
          (* swapval_reg has the value of M[yj] *)
          [ ARM.LDR (val_reg_M, addr_reg_M, "0") ] @
          (* save xi to M[yj] *)
          [ ARM.STR (showVarIdx xi, addr_reg_M, "0") ] @
          (* save swapval to xii *)
          [ ARM.MOV (showVarIdx xii, val_reg_M) ]
        end

        (* Works by pushing the link register (x30) on to the stack, doing the
           actual branching and then once we're done we pop the value from the
           stack back into the x30 register. This way we can handle recursion.
         *)
        (* NOT DONE TODO:*)
    | RSSA.Call (retvals, fname, inputs) =>
        let val filteredInputs = List.filter (fn (_, opt) => Option.valOf(opt) > ~2) inputs
            val filteredRetvals = List.filter (fn (_, opt) => Option.valOf(opt) > ~2) retvals
            val length = List.length filteredInputs
        in
          [ ARM.COMMENT("Call " ^ fname ^ "(" ^ Int.toString (List.length retvals) ^ "--") ] @
          [ ARM.STR ("x30", "sp", "-16")] @
          [ ARM.BL fname ] @
          [ ARM.LDR ("x30", "sp", "16")]
        end

        (* TODO: *)
    | RSSA.Uncall (retvals, fname, inputs) =>
        let
        in
          [ ARM.COMMENT("Call " ^ fname ^ "(" ^ Int.toString (List.length retvals) ^ "--") ] @
          [ ARM.STR ("x30", "sp", "-16") ] @
          [ ARM.BL fname ] @
          [ ARM.LDR ("x30", "sp", "16") ]
        end

    | RSSA.For (label, loopvariable, from, to, body) =>
        let val looplabel = showVarIdx label ^ "_loop_"
            val checklabel = showVarIdx label ^ "_loop_check"
            val idx_reg = newName "loop_idx"
            val finish_reg = newName "loop_finish_idx"
            val code = concatMap (compileStat symtab) body
        in
          [ ARM.COMMENT ("for (" ^ loopvariable ^ "=" ^  from ^ ";" ^ to ^ ")") ] @
          (* Place from and to in their registers*)
          [ ARM.MOV (idx_reg, from) ] @
          [ ARM.MOV (finish_reg, to) ] @
          (* jump to check *)
          [ ARM.B checklabel ] @
          (* loop label performs the code in body and increments the idx_reg  *)
          [ ARM.LABEL looplabel ] @
          code @
          [ ARM.ADD (idx_reg, idx_reg, "1") ] @
          (* check label compares and branches to loop label if idx_reg < finish_reg *)
          [ ARM.LABEL checklabel ] @
          [ ARM.CMP (idx_reg, finish_reg) ] @
          [ ARM.BLT looplabel ]
        end

    | RSSA.If (label, (condx, binop, condy), body) =>
        let val endlabel = showVarIdx label ^ "_false"
            val x = showVarIdx condx
            val y = showVarIdx condy
            val code1 = case binop of
                                RSSA.Equal => [ ARM.COMMENT ("if " ^ x ^ " == " ^ y) ] @
                                              [ ARM.CMP (x, y) ] @
                                              [ ARM.BNE endlabel ]

                              | RSSA.Neq => [ ARM.COMMENT ("if " ^ x ^ " != " ^ y) ] @
                                            [ ARM.CMP (x, y) ] @
                                            [ ARM.BEQ endlabel ]

                              | RSSA.Less => [ ARM.COMMENT ("if " ^ x ^ " < " ^ y) ] @
                                             [ ARM.CMP (x, y) ] @
                                             [ ARM.BGE endlabel]

                              | RSSA.Greater => [ ARM.COMMENT ("if " ^ x ^ " > " ^ y) ] @
                                                [ ARM.CMP (y, x) ] @
                                                [ ARM.BGE endlabel ]

                              | RSSA.Leq => [ ARM.COMMENT ("if " ^ x ^ " <= " ^ y) ] @
                                            [ ARM.CMP (x, y) ] @
                                            [ ARM.BGT endlabel ]

                              | RSSA.Geq => [ ARM.COMMENT ("if " ^ x ^ " >= " ^ y) ] @
                                            [ ARM.CMP (y, x) ] @
                                            [ ARM.BGT endlabel ]
                              | _ => raise Fail "binary operator not a comparison operator in if statement"
            val code2 = concatMap (compileStat symtab) body
        in
          code1 @
          code2 @
          [ ARM.LABEL endlabel ]
        end

    | RSSA.Skip =>
          [ ARM.NOP ]

          (*
          Symtab values looks like:
           (("foo", SOME 42), "foo_42_47")
           (("M", NONE), "M_50")
          *)
  (* compile function declaration *)
  fun compileARM (name, (_, _), (_, _, _), rssaCode, env, ds) =
    let
      (* first add all the variables from env to symtab *)
      val sym = List.foldl (fn ((var, idx), acc) =>
                              let val nm = newName (showVarIdx (var, idx))
                              in
                                 SymTab.bind (var, idx) nm acc
                              end) (SymTab.empty()) env 

      (* now add lists to symtab *)
      val (sym_n, arrayAllocCode) =
        List.foldl (fn (d, (sym_i, code)) =>
             (case d of 
               Hermes.ArrayDecl (nm, siz, _, _) =>
                        let val addr_reg = newName nm
                        in
                          (SymTab.bind (nm, NONE) addr_reg sym_i,
                           code @ arrayalloc(siz, addr_reg))
                        end 
             (* TODO: how to fill with values? | Hermes.ConstArrayDecl (nm, siz, _, _) => *)
             | _ => (sym_i, code)
             )
        ) (sym, []) ds
      val armCode = concatMap (fn stat => compileStat sym_n stat) rssaCode
      val wComment = if List.length arrayAllocCode > 0
                     then [ ARM.COMMENT "allocate memory on stack" ] @
                     arrayAllocCode
                     else []
    in
      (name, wComment @ armCode)
    end

  (* RSSA AST -> ARM AST *)
  fun compile fs =
     ARM.showProgram (List.map compileARM (RSSACompiler.convertToRSSA fs))

end
