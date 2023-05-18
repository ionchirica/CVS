
  function sum( xs: List<int> ): int
  {
    match( xs )
    {
      case Nil: 0
      case Cons( x, xs ): x + sum( xs )
    }
  }

  function append( xs: List<int>, ys: List<int> ): List<int>
  {
    match( xs )
    {
      case Nil: ys
      case Cons( x, xs ): Cons( x, append( xs, ys ) )
    }
  }

  lemma{:induction false} sum_append( xs: List<int>, ys: List<int> ): sum( append( xs, ys ) ) == sum( xs ) + sum( ys )
  {
  }
