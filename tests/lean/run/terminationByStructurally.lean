
def foo (n : Nat) : Nat := match n with
  | 0 => 0
  | n+1 => foo n
termination_by structural n

-- Test that this is indeed by structural recursion
example : foo (n + 3) = foo n := Eq.refl _


-- Check that we can still refer to a variable called `structural` in
-- the `termination_by` syntax
def bar (structural : Nat) : True := match structural with
  | 0 => .intro
  | structural+1 => bar structural
termination_by «structural»

namespace Errors
-- A few error conditions

/-- error: it is unchanged in the recursive calls -/
#guard_msgs in
def foo1 (n : Nat) : Nat := foo1 n
termination_by structural n

/--
error: its type Nat.le is an inductive family and indices are not variables
  n.succ.le 100
-/
#guard_msgs in
def foo2 (n : Nat) (h : n < 100) : Nat := match n with
  | 0 => 0
  | n+1 => foo2 n (by omega)
termination_by structural h

/--
error: one parameter bound in `termination_by`, but the body of Errors.foo3 only binds 0 parameters.
-/
#guard_msgs in
def foo3 (n : Nat) : Nat → Nat := match n with
  | 0 => id
  | n+1 => foo3 n
termination_by structural m => m

/--
error: failed to eliminate recursive application
  ackermann (n + 1) m
-/
#guard_msgs in
def ackermann (n m : Nat) := match n, m with
  | 0, m => m + 1
  | .succ n, 0 => ackermann n 1
  | .succ n, .succ m => ackermann n (ackermann (n + 1) m)
termination_by structural n

/--
error: failed to eliminate recursive application
  ackermann2 n 1
-/
#guard_msgs in
def ackermann2 (n m : Nat) := match n, m with
  | 0, m => m + 1
  | .succ n, 0 => ackermann2 n 1
  | .succ n, .succ m => ackermann2 n (ackermann2 (n + 1) m)
termination_by structural m

/--
error: The termination argument of a structurally recursive function must be one of the parameters 'n', but
  id n + 1
isn't one of these.
-/
#guard_msgs in
def foo4 (n : Nat) : Nat → Nat := match n with
  | 0 => id
  | n+1 => foo4 n
termination_by structural id n + 1


end Errors
