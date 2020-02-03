| Hermes.Update (updateOp, lVal, updateExp, pos) =>
        let val expVarIdx = newName "update_exp"
            val expCode = compileExp updateExp env expVarIdx
            val (lVal', lValCode) = compileLval lVal env
        in
            case lVal' of

                (* e.g. x += y + 3; *)
          RSSA.Var (x, x_idx) =>
            expCode @
            lValCode @
            [ RSSA.Assign ((x, x_idx),
                            SOME (x, x_idx),
                            SOME (convertUop updateOp),
                            SOME (RSSA.Var expVarIdx), (* R1 *)
                            NONE,                      (* binOp *)
                            NONE )]                    (* R2*)

                (* e.g. arr[x] += y; *)
        | RSSA.Array (m, var_idx) =>
            expCode @
            lValCode @
            [ RSSA.MemUpdate (m,
                              var_idx,
                              convertUop updateOp,
                              RSSA.Var expVarIdx,
                              NONE,
                              NONE )]

        end
