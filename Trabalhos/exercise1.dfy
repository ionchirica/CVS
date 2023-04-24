  /* -------------- Handout 1 - Exercise 1 ------------- *
   |                                                     |
   |           Cumulative Sums over Arrays               |
   |                                                     |
   |                                                     |
   |        Antonio Brejo           Ion Chirica          |
   |            58152                  64475             |
   * --------------------------------------------------- */

  /* ------------------------- 1a ------------------------- */
  /* -------------------- Function (1) -------------------- *
   | Recursively sums the elements in the range [down, up[. |
   * ------------------------------------------------------ */

  function sum( arr: array<int>, down: int, up: int ) : int
    reads arr
    requires 0 <= down <= up <= arr.Length
    decreases up
  {
    if  down >= up then 0
    else               arr[up - 1] + sum( arr, down, up - 1)
  }


  /* ----------------------- 1b ----------------------------- */
  /* --------------------- Method --------------------------- *
   | The desired behaviour is to calculate the sum over       |
   | the interval [down, up[, with down <= up.                |
   |                                                          |
   | To achieve the such behaviour we can note that the       |
   | Σ[ i, j [ is equal to the sum over Σ[ i, k [ + Σ[ k, j [ |
   | And so we use this observation to be our post-condition  |
   | Σ[ i, j [ == ∀ k ∈ [ i, j ] Σ [ i, k [ + Σ[ k, j [       |
   |                                                          |
   * -------------------------------------------------------- */

  method query( arr: array<int>, down: int, up: int ) returns (sum_query: int)
    requires arr.Length > 0
    requires 0 <= down <= up <= arr.Length
    ensures sum_query == sum( arr, down, up )

    ensures forall k :: down <= k <= up < arr.Length ==>  sum( arr, down, up) == sum( arr, down,  k ) +
                                                                        sum( arr,    k, up )
  {
    sum_query := 0;
    var ix := down;

    while( ix < up )
      invariant down <= ix <= up <= arr.Length

      invariant forall k :: down <= k <= ix ==>  sum( arr, down, ix) == sum( arr, down,  k ) +
                                                               sum( arr,    k, ix )
      invariant sum_query == sum(arr, down, ix )
    {
      sum_query := sum_query + arr[ix];
      ix := ix + 1;
    }
  }

  /* ----------------------------- 1c ------------------------------ */
  /* --------------------------- Method ---------------------------- *
   | The desired behaviour is the same as the previous method,       |
   | however we use an auxilary array that has pre-computed all      |
   | _prefix commulative_ sums over the given array.                 |
   |                                                                 |
   | For this to work we need to assert some properties of said      |
   | array:                                                          |
   |   - The first element must be 0.                            (1) |
   |   - Its length must be one unit greater than our target.    (2) |
   |   - It must satisfy that for any k then c[ k ] must be the  (3) |
   | sum from 0 to k in our target array.                            |
   |   - It must satisfy that for any i, j then c[ j ] - c[ i ]  (4) |
   | must be the sum from i to j in our target array.                |
   * ----------------------------------------------------------------*/

  method queryFast( arr: array<int>, c: array<int>, i: int, j: int )
    returns (r : int)
    requires arr.Length > 0
    requires c.Length > 0
    requires c[ 0 ] == 0
    requires c.Length == arr.Length + 1
    requires is_prefix_sum_for(arr, c)
    requires 0 <= i <= j <= arr.Length
    {
      assert c[ 0 ] == 0;
      assert forall k :: 0 <= k <= arr.Length ==> c[ k ] == sum( arr, 0, k );
      assert forall i, j :: 0 <= i <= j <= arr.Length ==> c[ j ] - c[ i ] == sum( arr, i, j );

      r := c[ j ] - c[ i ];
    }


  /* ------------------------- Predicate ---------------------- *
   | This predicate codifies the relation of being a prefix sum |
   | Essentially, it tries to sustain the property (3) and (4)  |
   | from the previous method.                                  |
   * ---------------------------------------------------------- */

  predicate is_prefix_sum_for( arr: array<int>, c: array<int> )
    reads arr, c
    requires 0 < arr.Length < c.Length
    requires c.Length == arr.Length + 1
  {
    c.Length == arr.Length + 1 &&
    c[ 0 ] == 0 &&
    forall    k :: 0 <= k <=     arr.Length ==> c[ k ]          == sum( arr, 0, k ) ==>
    forall i, j :: 0 <= i <= j <= arr.Length ==> c[ j ] - c[ i ] == sum( arr, i, j )
  }
