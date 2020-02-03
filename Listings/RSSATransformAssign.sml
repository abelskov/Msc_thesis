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
