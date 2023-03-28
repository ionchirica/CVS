/*
 mystery1( 3, 3 ) -> mystery1( 2, 4 )
 mystery1( 2, 4 ) -> mystery1( 1, 5 )
 mystery1( 1, 5 ) -> mystery1( 0, 6 )
 mystery1( 0, 6 ) =  6
*/

function mystery1(n: nat, m: nat): nat
  ensures mystery1( n, m ) == m + n
{
  if n == 0 then m
  else mystery1( n - 1, m + 1 )
}

/*
 mystery2( 3, 3 ) -> mystery2( 4, 2 )
 mystery2( 4, 2 ) -> mystery2( 5, 1 )
 mystery2( 5, 1 ) -> mystery2( 6, 0 )
 mystery2( 6, 0 ) =  6
*/

function mystery2(n: nat, m: nat): nat
  decreases m
  ensures mystery2( n, m ) == n + m
{
  if m == 0 then n
  else mystery2( n + 1, m - 1 )
}

/*
      n  m
  m3( 3, 4 )                           -> m1( 4, m3( 2, 4 ) )
  m1( 4, m1( 4, m3( 1, 4) ) )          -> m1( 4, m1( 4, m1( 4, m3( 0, 4)  ) ) )
  m1( 4, m1( 4, m1( 4, m3( 0, 4) ) ) ) -> m1( 4, m1( 4, m1( 4, 0 ) ) )
  m1( 4, m1( 4, m1( 4, 0 ) ) )         -> m1( 4, m1( 4, 4 ) )*/
/*
  m1( 4, 8 )                            = 12
*/
function mystery3(n: nat, m: nat): nat
  ensures mystery3( n, m ) == n * m
{
  if n == 0 then 0
  else mystery1( m, mystery3( n - 1, m ) )
}
/*
   mystery3(n , m) = n * m

       n, m
   m4( 3, 4 )                                     -> m3( 3, m4(3, 3) )
   m3( 3, m4( 3, 3 ))                             -> m3( 3, m3( 3, m4( 3, 2 ) ) )
   m3( 3, m3( 3, m4( 3, 2 ) ) )                   -> m3( 3, m3( 3, m3( 3, m4( 3, 1 ) ) ) )
   m3( 3, m3( 3, m3( 3, m4( 3, 1 ) ) ) )          -> m3( 3, m3( 3, m3( 3, m3( 3, m4( 3, 0 ) ) ) ) )
   m3( 3, m3( 3, m3( 3, m3( 3, m4( 3, 0 ) ) ) ) ) -> m3( 3, m3( 3, m3( 3, m3( 3, 1 ) ) ) )
   m3( 3, m3( 3, m3( 3, m3( 3, 1 ) ) ) )          -> m3( 3, m3( 3, m3( 3, 3 ) ) )
   m3( 3, m3( 3, m3( 3, 3 ) ) )                   -> m3( 3, m3( 3, 9 ) )
   m3( 3, m3( 3, 9 ) )                            -> m3( 3, 27)

   m3( 3, 27)                                      = 81
*/
function mystery4(n: nat, m: nat): nat
  ensures mystery4(n, m) == power(n, m)
{
  if m == 0 then 1
  else mystery3( n, mystery4( n, m - 1 ) )
}

function power(n: int, m:nat): int
  decreases m
{
  if m == 0 then 1
  else n * power(n, m - 1)
}

/* --------------------------------------------------------------------------------------------- */

lemma mystery1_correct( n: nat, m: nat )
  ensures mystery1(n, 0) == n
  ensures mystery1(n, m + 1) == 1 + mystery1( n, m )

lemma mys1c( n: nat, m: nat )
  ensures mystery1(n , m) == mystery1(m, n)
{
    mystery1_correct(n, m);
}

/* --------------------------------------------------------------------------------------------- */

lemma {:induction false} mysEq(n: nat, m: nat)
  ensures mystery1(n, m) == mystery2(n, m)
{

}
