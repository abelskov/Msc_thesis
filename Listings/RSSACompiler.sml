structure RSSACompiler :> RSSACompiler = struct

  exception Error of string*(int*int)

  fun concatWith [] s = ""
    | concatWith [x] s = x
    | concatWith (x :: xs) s = x ^ s ^ concatWith xs s

  fun invertStat s =
    case s of
      Hermes.Skip => Hermes.Skip
    | Hermes.Update (uop, lv, exp, pos) =>
         Hermes.Update (invertUop uop, lv, exp, pos)
    | Hermes.CondUpdate (cond, uop, lv, exp, pos) =>
         Hermes.CondUpdate (cond, invertUop uop, lv, exp, pos)
    | Hermes.Inc lval => Hermes.Dec lval
    | Hermes.Dec lval => Hermes.Inc lval
    | Hermes.Swap lvals => Hermes.Swap lvals
    | Hermes.CondSwap condlvals => Hermes.CondSwap condlvals
    | Hermes.Block (ds, ss, pos) =>
         Hermes.Block (ds, List.map invertStat (List.rev ss), pos)
    | Hermes.For (i, e1, e2, s, pos) =>
         Hermes.For (i, e2, e1, invertStat s, pos)
    | Hermes.Call call => Hermes.Uncall call
    | Hermes.Uncall call => Hermes.Call call
    | Hermes.Printf args => Hermes.Scanf args
    | Hermes.Scanf args => Hermes.Printf args
    | Hermes.Assert c => Hermes.Assert c

  and invertUop Hermes.Add = Hermes.Sub
    | invertUop Hermes.Sub = Hermes.Add
    | invertUop Hermes.XorWith = Hermes.XorWith
    | invertUop Hermes.RoL = Hermes.RoR
    | invertUop Hermes.RoR = Hermes.RoL

 fun concatMap f xs = List.concat (List.map f xs)

  fun stringConcatWith [] s = ""
    | stringConcatWith [x] s = x
    | stringConcatWith (x :: xs) s = x ^ s ^ stringConcatWith xs s

  
 fun  convertBinop Hermes.Plus = RSSA.Plus
    | convertBinop Hermes.Minus = RSSA.Minus
    | convertBinop Hermes.Times = RSSA.Times
    | convertBinop Hermes.Divide = RSSA.Divide
    | convertBinop Hermes.Modulo = RSSA.Modulo
    | convertBinop Hermes.Xor = RSSA.Xor
    | convertBinop Hermes.BAnd = RSSA.BAnd
    | convertBinop Hermes.BOr = RSSA.BOr
    | convertBinop Hermes.ShiftL = RSSA.ShiftL
    | convertBinop Hermes.ShiftR = RSSA.ShiftR
    | convertBinop Hermes.Equal = RSSA.Equal
    | convertBinop Hermes.Less = RSSA.Less
    | convertBinop Hermes.Greater = RSSA.Greater
    | convertBinop Hermes.Neq = RSSA.Neq
    | convertBinop Hermes.Leq = RSSA.Leq
    | convertBinop Hermes.Geq = RSSA.Geq
 
  fun convertUop Hermes.Add = RSSA.Add
    | convertUop Hermes.Sub = RSSA.Sub
    | convertUop Hermes.XorWith = RSSA.XorWith
    | convertUop Hermes.RoL = RSSA.RoL
    | convertUop Hermes.RoR = RSSA.RoR

  val counter = ref 1

  fun newName name = 
    let 
      val n = !counter
      val () = counter := !counter + 1
    in
      (name, SOME n)
    end

  fun newIndex () =
    let
      val n = !counter
      val () = counter := !counter + 1
    in
      n
    end

  fun extractLvalName (Hermes.Var (x, _)) _ = x
    | extractLvalName (Hermes.Array (m, _, _)) _ = m

    (* (String * Int option) * String -> (String * Int) *)
  fun lookup [] varname = (varname, ~2)
    | lookup ((x, NONE) :: env) varname =
      let val cmp = String.compare(x, varname)
      in
        if cmp = EQUAL
        then (x, ~1)
        else lookup env varname
      end
    | lookup ((x, SOME idx) :: env) varname =
      let val cmp = String.compare(x, varname)
      in
        if cmp = EQUAL
        then (x, idx)
        else lookup env varname
      end
 
  (* Idea: Convert a 'Hermes.lVal' into an 'RSSA.lVal' by translating the
   * array-indexing expression to code and use the variable that the result
   * of evaluating the expression ends up in. This is a 'var' and not a
   * 'var_idx' because the RSSA table doesn't have subscript indices for any
   * array-index variables.
   *)
   (* TODO: might not want a new name for the variable. Maybe just give it index
   * NONE to begin with *)
  fun compileLval (Hermes.Var (x, _)) env =
    let val (_, ix) = lookup env x
        val (var, idx) = if ix < ~1 then (x, SOME ix) else newName x
    in
      (RSSA.Var (var, idx), [])
    end
    | compileLval (Hermes.Array (m, e, _)) env =
        let val var_idx = newName "lval_idx"
            val code = compileExp e env var_idx 
        in
      (RSSA.Array (m, var_idx), code)
        end

  and compileExp e env (dst, dst_idx) =
    case e of
         (* FIXME: Currently the destination variable 'dst' is passed to 'compileExp'
          * so that the code generated here can place the result in 'dst'. But what
          * if the expression is just a variable reference already? Then there's no
          * need for creating a new variable.
 
          * One solution could be to remove 'dst' from 'compileExp's args and instead
          * let it return a 2-tuple, kind of like 'compileLval' where the first value
          * is... Hmm... either a 'var' (string) or an 'RSSA.lVal'... and the second
          * is an 'RSSA.instr list'.

          * Then in the case of 'Hermes.Rval' below, the variable name can be returned.
          *)
      Hermes.Rval lv => let val (lval, lvalcode) = compileLval lv env 
                        in (case lval of 
                                 RSSA.Var (x, x_idx) =>
                                 lvalcode @ [ RSSA.Assign ((dst, dst_idx),
                                              SOME (x, x_idx),
                                              NONE,
                                              NONE,
                                              NONE,
                                              NONE )] 
                              | RSSA.Array (m, var_idx) =>
                                 lvalcode @ [ RSSA.Assign ((dst, NONE),
                                              NONE,
                                              NONE,
                                              SOME (RSSA.Array(m, var_idx)),
                                              NONE,
                                              NONE )]
                           )
                        end
    | Hermes.Const (c, pos) => [ RSSA.Assign ((dst, dst_idx),
                                 NONE (* TODO: Check if this could be RSSA.Var (c, NONE) and then it does not have to be an option *),
                                 NONE,
                                 SOME (RSSA.Var (c, NONE)),
                                 NONE,
                                 NONE)]

    | Hermes.Bin (binOp, e1, e2, pos) =>
        let val e1VarIdx  = newName "bin"
            val e1Code = compileExp e1 env e1VarIdx
            val e2VarIdx  = newName "bin"
            val e2Code = compileExp e2 env e2VarIdx
        in
          e1Code @ e2Code @ [ RSSA.Assign ((dst, dst_idx),
                              SOME (dst, dst_idx),
                              SOME (RSSA.Add),
                              SOME (RSSA.Var e1VarIdx),
                              SOME (convertBinop binOp),
                              SOME (RSSA.Var e2VarIdx) )]
        end
    | _ => raise Fail "compileExp: not done"

  (* compileCond : exp * env * string * string -> (precode, cond) *)
  and compileCond (cond as (Hermes.Bin (h_binop, e1, e2, pos)), env, x_dst, y_dst) =
    let val r_binop = convertBinop h_binop
        val ce1 = compileExp e1 env x_dst
        val ce2 = compileExp e2 env y_dst
    in
      (ce1 @ ce2, (x_dst, r_binop, y_dst))
      (* (ce1 @ ce2, ((x_dst, NONE), r_binop, (y_dst, NONE))) *)
    end
    | compileCond _ = raise Fail "compileCond not fully implemented"

  (* compileStat : stat * env -> RSSA.instrs list *)
  fun compileStat stat env =
    case stat of
      Hermes.Skip => [RSSA.Skip]
    | Hermes.Update (updateOp, lVal, updateExp, pos) =>
        let val expVarIdx = newName "update_exp"
            val expCode = compileExp updateExp env expVarIdx (* compiles the value into expVar*)
            val (lVal', lValCode) = compileLval lVal env
        in
            case lVal' of
               (* FIXME: The two 'lVal' args in 'RSSA.Assign' and 'RSSA.MemUpdate'
                * are based on 'Converting assignments and calls from RIL to RSSA'
                * table in which there's always 'R1' and 'R2'. But I think where
                * these are found inside 'Hermes.Update' is actually in 'updateExp'
                * expression.

                * So maybe it's possible to extract the two operands...
                * Or maybe they need to be something else...
                *)
                (* e.g. x += y + 3; *)
          RSSA.Var (x, x_idx) =>
            expCode @ lValCode @
            [ RSSA.Assign ((x, x_idx),
                            SOME (x, x_idx),
                            SOME (convertUop updateOp),
                            SOME (RSSA.Var expVarIdx), (* R1 *)
                            NONE,    (* binOp *)
                            NONE )]  (* R2*)
                (* e.g. arr[x] += y; *)
        | RSSA.Array (m, var_idx) =>
            expCode @ lValCode @
            [ RSSA.MemUpdate (m,
                              var_idx,
                              convertUop updateOp,
                              RSSA.Var expVarIdx,
                              NONE,
                              NONE )]
        
        end
    | Hermes.CondUpdate (cond, updateOp, lv, updateExp, pos) =>
              (* if (cond) lv updateOp updateExp *)
        let
          val x_dst = newName "_cond"
          val y_dst = newName "_cond"
          val (code, ccond) = compileCond (cond, env, x_dst, y_dst)
          val update = compileStat (Hermes.Update (updateOp, lv, updateExp, pos)) env
        in
          code @ [ RSSA.If (newName "label", ccond, update) ]
        end
    | Hermes.Inc (lv, pos) =>
        (case lv of
              (* x++; *)
          Hermes.Var (s, pos) =>
            [ RSSA.Assign ((s, NONE),
                           SOME (s, NONE),
                           SOME RSSA.Add,
                           SOME (RSSA.Var ("1", NONE)),
                           NONE,
                           NONE) ]
              (* arr[x]++; *)
        | Hermes.Array (s, e, pos) =>
            let val expVarIdx = newName "arr_idx"
                val expCode = compileExp e env expVarIdx (* compiles the code into expVar *)
            in
              expCode @ [ RSSA.MemUpdate (s,
                                          expVarIdx,
                                          RSSA.Add,
                                          RSSA.Var ("1", NONE),
                                          NONE,
                                          NONE )]
            end
        )
    | Hermes.Dec (lv, pos) =>
        (case lv of
              (* x--; *)
          Hermes.Var (s, pos) =>
            [ RSSA.Assign ((s, NONE),
                           SOME (s, NONE),
                           SOME RSSA.Sub,
                           SOME (RSSA.Var ("1", NONE)),
                           NONE,
                           NONE) ]
              (* arr[x]--; *)
        | Hermes.Array (s, e, pos) =>
            let val expVarIdx = newName "arr_idx"
                val expCode = compileExp e env expVarIdx (* compiles the code into expVar *)
            in
              expCode @ [ RSSA.MemUpdate (s,
                                          expVarIdx,
                                          RSSA.Sub,
                                          RSSA.Var ("1", NONE),
                                          NONE,
                                          NONE )]
            end
        )
              (* x <-> y *)
    | Hermes.Swap (lv1 as Hermes.Var (s, _), lv2 as Hermes.Var (s2, _), _) =>
          [ RSSA.AssignSwap ((s, NONE), (s2, NONE), (s2, NONE), (s, NONE)) ]

              (* M[x] <-> N[y] *)
    | Hermes.Swap (lv1 as Hermes.Array (s1, e1, _), lv2 as Hermes.Array (s2, e2, _), _) =>
          let val tmp1 = newName "arr_idx"
              val tmp2 = newName "arr_idx"
              val code1 = compileExp e1 env tmp1
              val code2 = compileExp e2 env tmp2
          in
            code1 @ code2 @ [ RSSA.MemSwap(s1, tmp1, s2, tmp2) ]
          end

              (* x <-> M[x] *)
    | Hermes.Swap (lv1 as Hermes.Var (s, _), lv2 as Hermes.Array (s2, e, _), _) =>
          let val tmp1 = newName "arr_idx"
              val code1 = compileExp e env tmp1
          in
            code1 @ [ RSSA.VarMemSwap((s, NONE), s2, tmp1, (s, NONE)) ]
          end

              (* M[x] <-> x *)
              (* redirect to x <-> M[x] just above *)
    | Hermes.Swap (lv1 as Hermes.Array (s, e, _), lv2 as Hermes.Var (s2, _), pos) =>
          compileStat (Hermes.Swap (lv2, lv1, pos)) env
    | Hermes.CondSwap (cond, lv1, lv2, pos) => 
        let
          val x_dst = newName "if_cond_x"
          val y_dst = newName "if_cond_y"
          val (code, ccond) = compileCond (cond, env, x_dst, y_dst)
          val swap = compileStat (Hermes.Swap (lv1, lv2, pos)) env
        in
          code @ [ RSSA.If (newName "label", ccond , swap) ]
        end
    | Hermes.Block (ds, ss, pos) =>
        raise Fail "ShouldNotHappen"

              (* for (i=from; to) {
               *   body..
               * }
               *)
    | Hermes.For (i, Hermes.Const (from, _), Hermes.Const (to, _), s as Hermes.Block(_, stats, _), _) =>
        let val label = newName "for"
            val body = concatMap (fn stat => compileStat stat env) stats
        in
          [ RSSA.For (label, i, from, to, body) ]
        end
              (* (y', ...) := call foo(x', ...) *)
    | Hermes.Call (fname, lvs, _) =>
        let val xvals = List.map (fn lv => extractLvalName lv env) lvs
            val options = List.tabulate (List.length xvals, (fn n => NONE))
            val var_idxs = ListPair.zip(xvals, options)
            val yvals = xvals
            val var_idys = ListPair.zip(yvals, options)
        in
          [ RSSA.Call (var_idys, fname, var_idxs) ]
        end

              (* (x', ...) := uncall foo(y', ...) *)
    | Hermes.Uncall (fname, lvs, _) =>
        let val xvals = List.map (fn lv => extractLvalName lv env) lvs
            val options = List.tabulate (List.length xvals, (fn n => NONE))
            val var_idxs = ListPair.zip(xvals, options)
            val yvals = xvals
            val var_idys = ListPair.zip(yvals, options)
        in
          [ RSSA.Uncall (var_idys, fname, var_idxs) ]
        end
    | Hermes.Printf (_, _, _) => [ RSSA.Skip ]
    | _ => raise Fail "compileStat: not done"

  fun rssaTransform code env =
    (case code of
          RSSA.Skip => ([ RSSA.Skip ], env)
        | RSSA.Assign ((x, iopt), var, uop, lv1, binop, lv2) =>
            let val lookup_val = lookupVarIdx var env
                val x_i = if lookup_val = NONE then var else lookup_val
                val x_ii = (case iopt of
                               NONE => (x, SOME (newIndex()))
                             | SOME idx => (x, SOME idx))
                val new_env = updateEnv x_ii env []
            in
              ( [ RSSA.Assign (x_ii, x_i, uop, lv1, binop, lv2) ], new_env)
            end
        | RSSA.MemUpdate (array, (x, iopt), updateOp, lVal1, binOp, lVal2) =>
            let val var_x = (case iopt of
                                  NONE => (x, SOME (newIndex()))
                                | SOME idx => (x, SOME idx)
                            )
                val new_env = updateEnv var_x env []
            in
              ( [ RSSA.MemUpdate (array, var_x, updateOp, lVal1, binOp, lVal2) ], new_env)
            end

          (* Inputs to AssignSwap are (string * int option) *)
        | RSSA.AssignSwap ((x2, _), (y2, _), (y1, _), (x1, _)) =>
            let (* Lookup current values *)
                (* (String * Int) *)
                val (idx_i, idx_iopt) = lookup env x1
                val (idy_i, idy_iopt) = lookup env y1
                (* Generate new values *)
                val idx_ii = (idx_i, SOME (newIndex()))
                val idy_ii = (idy_i, SOME (newIndex()))
                (* Update environment with new values *)
                val env_i = updateEnv idx_ii env []
                val env_ii = updateEnv idy_ii env_i []
            in
              ( [RSSA.AssignSwap (idx_ii,
                                  idy_ii,
                                 (idy_i, SOME idy_iopt),
                                 (idx_i, SOME idx_iopt)
                                 )], env_ii)
            end

            (* TODO: need to look over this again. maybe need to lookup the newest var_idx for index? *)
            (* M[xi] <-> N[yj] *)
        | RSSA.MemSwap (arr_M, (x, xopt), arr_N, (y, yopt)) =>
            let val var_x = (case xopt of
                                  NONE => (x, SOME (newIndex()))
                                | SOME idx => (x, SOME idx)
                            )
                val var_y = (case yopt of
                                  NONE => (y, SOME (newIndex()))
                                | SOME idx => (y, SOME idx)
                            )
                val env_i = updateEnv var_x env []
                val env_ii = updateEnv var_y env_i []
            in
              ( [ RSSA.MemSwap (arr_M, var_x, arr_N, var_y) ], env_ii)
            end

            (* xii := array[yj] := xi*)
        | RSSA.VarMemSwap ((var_idx2, _), array, var_idy, (var_idx, _)) =>
            let val (idx_i, idx_iopt) = lookup env var_idx
                val newIdx = newIndex()
                val env_i = updateEnv (idx_i, SOME newIdx) env []
            in
              ( [ RSSA.VarMemSwap ((var_idx2, SOME newIdx), array, var_idy, (idx_i, SOME idx_iopt)) ], env_i)
            end

        | RSSA.Call (var_idys, fname, var_idxs) => 
            let 
                (* LOAD *)
              val (idxs, _) = ListPair.unzip var_idxs
              val new_idxs = List.map (fn (x, i) => (x, SOME i)) (List.map (lookup env) idxs)
                (* SAVE *)
              val yvals = List.rev (List.foldl (fn ((y, iopt), acc) =>
                                        let val (a, b) = lookup env y (* lookup y so that arrays do not get a new index *)
                                            val subscript = if b < ~1 then b
                                                            else newIndex() (* TODO: hacky solution rn where if
                                                                                     things are not in environment
                                                                                     they must be arrays and then
                                                                                     they will have a subscript of ~2
                                                                                     from lookup function 
                                                                             *)
                                        in
                                          (a, SOME subscript) :: acc
                                        end
                                        ) [] var_idys)

              val updated_env = List.foldl (fn (x, acc) =>
                                            let val new_env = updateEnv x acc []
                                            in new_env
                                            end) env yvals 

            in
              ( [ RSSA.Call (yvals, fname, new_idxs) ], updated_env)
            end

        | RSSA.Uncall (var_idxs, fname, var_idys) =>
            let 
                (* LOAD Y FROM ENVIRONMENT *)
                val (idys, _) = ListPair.unzip var_idys
                val new_idys = List.map (fn (x, i) => (x, SOME i)) (List.map (lookup env) idys)
                (* SAVE XS TO ENVIRONMENT*)
                val xvals = List.rev (List.foldl (fn ((x, iopt), acc) =>
                                          let val (a, b) = lookup env x
                                              val subscript = if b < ~1 then b
                                                              else newIndex()
                                          in
                                            (x, SOME subscript) :: acc
                                          end
                                          ) [] var_idxs)
                val updated_env = List.foldl (fn (x, acc) =>
                                            let val new_env = updateEnv x acc []
                                            in new_env
                                            end) env xvals 
            in
              ( [ RSSA.Uncall (xvals, fname, new_idys) ], updated_env)
            end
            (* compiling the subexpressions in the body *)
        | RSSA.For (label, i, from, to, instrs) =>
            let val (rssaCode, env_n) = List.foldl (fn (instr, (code, env_i)) =>
                                      let val (newinstr, env_ii) = rssaTransform instr env_i
                                      in (code @ newinstr, env_ii)
                                      end) ([], env) instrs 
            in
              ( [ RSSA.For (label, i, from, to, rssaCode) ], env_n)
            end
            (* compiling the subexpressions in the body *)
        | RSSA.If (label, (var_idx, binop, var_idy), instrs) =>
            let val (rssaCode, env_n) = List.foldl (fn (instr, (code, env_i)) =>
                                      let val (newinstr, env_ii) = rssaTransform instr env_i
                                      in (code @ newinstr, env_ii)
                                      end) ([], env) instrs 
            in
              ( [ RSSA.If (label, (var_idx, binop, var_idy), rssaCode) ], env_n)
            end
    )

  (* returns a string that initializes local variables *)
  and compileLocalInits decl =
    case decl of
      Hermes.VarDecl (varname, _, _) =>
        "  " ^ "initialize " ^ varname ^ " to 0" ^ "\n"
    | Hermes.ConstDecl (varname, value, _, _) =>
        "  " ^ "initialize const " ^ varname ^ " to " ^ value ^ "\n"
    | Hermes.ArrayDecl (varname, size, _, _) =>
        "  " ^ "initialize " ^ varname ^ "[0.." ^ size ^ "]" ^ " to 0" ^ "\n"
    | _ => raise Fail "ArgumentException"
  

  (* 
  * Input: (String * Int option) option * (String * Int option) List
  * Output: (String * Int option) option
  *)
  and lookupVarIdx NONE _ = NONE
    | lookupVarIdx (SOME (varname, old_idx)) [] = NONE
    | lookupVarIdx (SOME (varname, old_idx)) ((x, new_idx) :: env) =
      let val cmp = String.compare(x, varname)
      in
        if cmp = EQUAL
        then (SOME (x, new_idx))
        else lookupVarIdx (SOME (varname, old_idx)) env
      end

  (* Replaces (y, y_idx) in environment with (x, x_idx) if it exists *)
  (* (string * int option) * (string * int option) list -> (string * int option) list *)
  and updateEnv (x, x_idx) [] res = res
    | updateEnv (x, x_idx) ((y, y_idx) :: env) res =
        let val cmp = String.compare(x, y)
        in
          if cmp = EQUAL
          then updateEnv (x, x_idx) env ((x, x_idx) :: res)
          else updateEnv (x, x_idx) env ((y, y_idx) :: res)
        end

  (* Hermes.Decl -> (string * int option) *)
  and compileLocalFinits decl env =
    case decl of
      Hermes.VarDecl (varname, _, _) =>
        [ lookup env varname]
    | Hermes.ConstDecl (varname, value, _, _) => []
    | Hermes.ArrayDecl (varname, size, _, _) => []
    | _ => raise Fail "ArgumentException"

  and compileLocalArrayFinits decl =
    case decl of
      Hermes.VarDecl (varname, _, _) => ""
    | Hermes.ConstDecl (varname, value, _, _) => "" (* TODO: do we finit a const ? *)
    | Hermes.ArrayDecl (varname, size, _, _) => "  " ^ "0 := " ^ varname ^ "[0.." ^ size ^ "]" ^ "\n"
    | _ => raise Fail "ArgumentException"

  fun updateVarIdx env (x, idx) =
    [ lookup env x ]

  (* NOTE: Instead of representing a VarDecl as the assignment instruction
   * of a variable to itself with R1 `op` R2 being nothing, either don't do
   * anything or collect something into an 'env' -- just not sure what's
   * needed yet.
   *
   * TODO: One thing that could be useful is a lookup table for constants
   * (both scalars and indexing into arrays). For the code generation, when
   * we see 'x' or 'M[x]', we could then check to see if 'x' or 'M' are in
   * the constant table of 'env' and replace it with a constant instead.
   *)
  fun compileEnv (decl, env) =
      case decl of
          Hermes.VarDecl (name, typ, pos) => (name, NONE) :: env
        | Hermes.ConstDecl (name, value, typ, pos) => env
        | Hermes.ConstArrayDecl (name, size, values, typ, pos) => env
        | Hermes.PubDecl (name, value, typ, pos) => env
        | Hermes.ArrayDecl (name, size, typ, pos) => env (* not sure *)

  fun compileDecl env decl =
      case decl of
          Hermes.VarDecl (name, typ, pos) =>
            let val (lookupvar, idx) = lookup env name
                val subscript = if idx < 0 then ~1 else idx
            in
              (lookupvar, subscript)
            end
        | Hermes.ArrayDecl (name, size, typ, pos) => (name, ~1)
        | _ => ("", ~1)

  (* HERMES Procedure -> RSSA *)
  (* returns list of basic blocks *)
  fun compileRil (name, decls, body as Hermes.Block(ds, stats, _), pos) =
      let val env = List.foldl compileEnv [] (decls @ ds)
          val args = List.map (compileDecl env) decls
          val retvals = args
          val localInits = List.foldl (fn (x, acc) => acc ^ compileLocalInits x) "" ds
          val localFinits = List.foldl (fn (x, acc) => acc @ compileLocalFinits x env) [] ds
          val localArrayFinits = List.foldl (fn (x, acc) => acc ^ compileLocalArrayFinits x) "" ds
          val rBody = invertStat body
          val code = concatMap (fn stat => compileStat stat env) stats
      in
          (name, (args, retvals), (localInits, localFinits, localArrayFinits), code, env, ds)
      end
    | compileRil (name, _, _, pos) =
        raise Error ("Non-block statement as function body in '" ^ name ^ "'", pos)

  (* compile function declaration *)
  (* RSSA -> RSSA *)
  fun compileRSSA (name, (args, retvals), (localInits, localFinits, localArrayFinits), code, env_0, ds) =
    let val (rssaCode, env_n) = List.foldl
                                     (fn (instr, (acc, env_i)) =>
                                      let val (newlytransformedinstruction, env_ii) = rssaTransform instr env_i
                                      in (acc @ newlytransformedinstruction, env_ii)
                                      end) ([], env_0) code
        val updatedFinits =  List.foldl (fn ((x, idx), acc) => acc @ [lookup env_n x]) [] localFinits
        val updatedRetvals = List.foldl (fn ((x, idx), acc) => acc @ [lookup env_n x]) [] retvals
    in
      (* name, args and localInits stay the same in RIL and RSSA. *)
      (name, (args, updatedRetvals), (localInits, updatedFinits, localArrayFinits), rssaCode, env_n, ds)
    end

  (* Transforms/Optimizes the AST
   * Does two transformations on the code. First to RIL, then to RSSA.
   * HERMES -> RSSA -> RSSA *)
  fun compile fs =
    RSSA.showProgram (convertToRSSA fs)

  and convertToRSSA fs =
    (List.map compileRSSA (List.map compileRil fs))

end
