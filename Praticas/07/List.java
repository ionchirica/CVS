/*@
  predicate Node( Node n; Node nn, int v ) = n.next |-> nn &*& n.val |-> v;
  predicate List( Node n; list<int> elems ) = n == null ? emp &*& elems == nil :
    Node(n, ?nn, ?v) &*& List(nn, ?tail) &*& elems == cons( v, tail );
  predicate ListInv( List l; list<int> elems ) = l.head |-> ?h &*& List(h, elems);
 @*/

class Node
{
  Node next;
  int val;

  Node()
  //@ requires true;
  //@ ensures Node(this, null, 0);
  {
    next = null;
    val = 0;
  }

  Node (int v, Node next)
  //@ requires true;
  //@ ensures Node(this, next, v);
  {
    this.next = next;
    this.val = v;
  }

  void setNext( Node next )
  //@ requires Node( this, _, ?v ) &*& Node( next, _, _ );
  //@ ensures Node( this, next, v );
    {
      this.next = next;
    }

  void setVal( int v )
  //@ requires Node( this, ?nn, _ );
  //@ ensures Node( this, nn, v );
    {
      this.val = v;
    }
}

class List
{
  Node head;

  public List()
  //@ requires true;
  //@ ensures ListInv( this, nil );
  {
   head = null;
  }

  void reverseList()
  //@ requires ListInv( this, ?l );
  //@ ensures ListInv( this, reverse( l ) );
  {
    Node n = null;
    //@ open ListInv( this, l );

    while( head != null )
    /*@
      invariant head |-> ?h &*& List(h, ?l1) &*& List(n, ?l2) &*&
      l == append( reverse( l2), l1 ); @*/
    {
      Node k = head.next;
      head.next = n;
      n = head;
      head = k;

      //@ assert l1 == cons( ?v, ?tail0 ) &*& l == append( reverse( l2 ), cons( v, tail0 ) );
      //@ reverse_reverse( cons(v, tail0) );
      //@ reverse_append( reverse(cons( v, tail0 )), l2 );
      //@ append_assoc( reverse(tail0), cons(v, nil), l2 );
      //@ reverse_append( reverse(tail0), cons(v, l2));
      //@ reverse_reverse( tail0 );
    }
    //@open List(h, l1);
    head = n;
    //@append_nil(reverse(l2));
  }
}
