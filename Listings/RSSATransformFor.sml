| RSSA.For (label, i, from, to, instrs) =>
    let val (rssaCode, env_n) =
          List.foldl (fn (instr, (code, env_i)) =>
            let val (newinstr, env_ii) = rssaTransform instr env_i
            in (code @ newinstr, env_ii)
            end) ([], env) instrs 
    in
      ( [ RSSA.For (label, i, from, to, rssaCode) ], env_n)
    end
