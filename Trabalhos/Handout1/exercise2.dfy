 /* ------------ Handout 1 - Exercise 2 ------------ *
  |                                                  |
  |      Functional Lists and Imperative Arrays      |
  |                                                  |
  |                                                  |
  |      Antonio Brejo           Ion Chirica         |
  |          58152                  64475            |
  * ------------------------------------------------ */


  datatype List<T> = Nil | Cons( head: T, tail: List<T> )


  /* -------------- Function (1) ------------- *
   | Recursively increments the returns value  |
   | until the list is empty                   |
   * ----------------------------------------- */
  function list_length<T>( l: List<T> ) : nat
    decreases l
  {
    match l
      case Nil => 0
      case Cons(_, r) => 1 + list_length ( r )
  }


  /* ------- Function (2) ------- *
   | Checks if an element T is at |
   | certain position in the list |
   * ---------------------------- */

  function list_exists_at<T(==)> ( l: List<T>, pos: nat, element: T ) : bool
    requires 0 <= pos <= list_length( l )
  {
    match l
      case Nil => false
      case Cons( x, r ) => if x == element && pos == 0 then true
                     else if  x != element && pos == 0 then false
                     else    list_exists_at( r, pos - 1, element )
  }


  /* ---------- Function (3) ---------- *
   | Checks if an element T is a member |
   | of the list                        |
   * ---------------------------------- */

  function mem<T(==)> ( x: T, l: List<T> ) : bool
  {
     match l
      case Nil => false
      case Cons( h, r ) => if   h == x then true
                          else mem( x, r )
  }

  /* -------------------- Method ---------------------- *
   | The desired behaviour is to return a list with     |
   | shape, order and elements as an input array.       |
   |                                                    |
   | We can assert the shape property ensuring that     |
   | both the array and the list have the same length.  |
   |                                                    |
   | The order is mantained by the fact that the array  |
   | is being iterated backwards and the elements are   |
   | being appended to the head of the list.            |
   |                                                    |
   | To guarantee that all members from the array were  |
   | inserted into the list we use the function (2), (3)|
   |                                                    |
   | There should be a careful thought to the fact the  |
   | array iterator (ix) is decreasing.                 |
   * -------------------------------------------------- */

  method from_array<T>( a: array<T> ) returns ( l: List<T> )
    requires a.Length > 0
    ensures a.Length == list_length ( l )
    ensures forall k :: 0 <= k < a.Length ==> list_exists_at( l, k, a[k] )
    ensures forall k :: mem( k, l ) ==> exists i :: 0 <= i < a.Length && a[i] == k
  {
    var ix := a.Length - 1;
    l := Nil;

    while( ix >= 0 )
      invariant -1 <= ix <= a.Length - 1
      invariant list_length ( l ) == a.Length - ix - 1
      invariant forall k :: ix < k < a.Length ==> list_exists_at( l, k - ix - 1, a[k] )
      invariant forall k :: mem( k, l ) ==> exists i :: ix < i < a.Length && a[i] == k
    {
      l := Cons( a[ix], l );
      ix := ix - 1;
    }
  }
