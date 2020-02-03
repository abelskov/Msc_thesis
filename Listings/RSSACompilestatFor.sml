| Hermes.For (i,
              Hermes.Const (from, _),
              Hermes.Const (to, _),
              s as Hermes.Block(_, stats, _),
              _) =>
    let val label = newName "for"
        val body = concatMap (fn stat => compileStat stat env) stats
    in
      [ RSSA.For (label, i, from, to, body) ]
    end
