/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

notation, basic datatypes and type classes
-/
prelude

notation `Prop`  := Type 0
notation `Type₂` := Type 2
notation `Type₃` := Type 3

/- Logical operations and relations -/

reserve prefix `¬`:40
reserve prefix `~`:40
reserve infixr ` ∧ `:35
reserve infixr ` /\ `:35
reserve infixr ` \/ `:30
reserve infixr ` ∨ `:30
reserve infix ` <-> `:20
reserve infix ` ↔ `:20
reserve infix ` = `:50
reserve infix ` ≠ `:50
reserve infix ` ≈ `:50
reserve infix ` ~ `:50
reserve infix ` ≡ `:50
reserve infixl ` ⬝ `:75
reserve infixr ` ▸ `:75
reserve infixr ` ▹ `:75

/- types and type constructors -/

reserve infixr ` ⊕ `:30
reserve infixr ` × `:35

/- arithmetic operations -/

reserve infixl ` + `:65
reserve infixl ` - `:65
reserve infixl ` * `:70
reserve infixl ` / `:70
reserve infixl ` % `:70
reserve prefix `-`:100
reserve infix ` ^ `:80

reserve infixr ` ∘ `:90                 -- input with \comp

reserve infix ` <= `:50
reserve infix ` ≤ `:50
reserve infix ` < `:50
reserve infix ` >= `:50
reserve infix ` ≥ `:50
reserve infix ` > `:50

/- boolean operations -/

reserve infixl ` && `:70
reserve infixl ` || `:65

/- set operations -/

reserve infix ` ∈ `:50
reserve infix ` ∉ `:50
reserve infixl ` ∩ `:70
reserve infixl ` ∪ `:65
reserve infix ` ⊆ `:50
reserve infix ` ⊇ `:50
reserve infix ` ⊂ `:50
reserve infix ` ⊃ `:50
reserve infix ` \ `:70

/- other symbols -/

reserve infix ` ∣ `:50
reserve infixl ` ++ `:65
reserve infixr ` :: `:67
reserve infixl `; `:1

universe variables u v

inductive poly_unit : Type u
| star : poly_unit

inductive unit : Type
| star : unit

inductive true : Prop
| intro : true

inductive false : Prop

inductive empty : Type

def not (a : Prop) := a → false
prefix `¬` := not

inductive eq {A : Type u} (a : A) : A → Prop
| refl : eq a

inductive heq {A : Type u} (a : A) : Π {B : Type u}, B → Prop
| refl : heq a

structure prod (A : Type u) (B : Type v) :=
(fst : A) (snd : B)

inductive and (a b : Prop) : Prop
| intro : a → b → and

def and.elim_left {a b : Prop} (H : and a b) : a :=
and.rec (λ Ha Hb, Ha) H

def and.left := @and.elim_left

def and.elim_right {a b : Prop} (H : and a b) : b :=
and.rec (λ Ha Hb, Hb) H

def and.right := @and.elim_right

inductive sum (A : Type u) (B : Type v)
| inl {} : A → sum
| inr {} : B → sum

inductive or (a b : Prop) : Prop
| inl {} : a → or
| inr {} : b → or

def or.intro_left {a : Prop} (b : Prop) (Ha : a) : or a b :=
or.inl Ha

def or.intro_right (a : Prop) {b : Prop} (Hb : b) : or a b :=
or.inr Hb

structure sigma {A : Type u} (B : A → Type v) :=
mk :: (fst : A) (snd : B fst)

-- pos_num and num are two auxiliary datatypes used when parsing numerals such as 13, 0, 26.
-- The parser will generate the terms (pos (bit1 (bit1 (bit0 one)))), zero, and (pos (bit0 (bit1 (bit1 one)))).
-- This representation can be coerced in whatever we want (e.g., naturals, integers, reals, etc).
inductive pos_num : Type
| one  : pos_num
| bit1 : pos_num → pos_num
| bit0 : pos_num → pos_num

namespace pos_num
  def succ (a : pos_num) : pos_num :=
  pos_num.rec_on a (bit0 one) (λ n r, bit0 r) (λ n r, bit1 n)
end pos_num

inductive num : Type
| zero  : num
| pos   : pos_num → num

namespace num
  open pos_num
  def succ (a : num) : num :=
  num.rec_on a (pos one) (λ p, pos (succ p))
end num

inductive bool : Type
| ff : bool
| tt : bool

class inductive decidable (p : Prop)
| is_false : ¬p → decidable
| is_true :  p → decidable

@[reducible]
def decidable_pred {A : Type u} (r : A → Prop) :=
Π (a : A), decidable (r a)

@[reducible]
def decidable_rel {A : Type u} (r : A → A → Prop) :=
Π (a b : A), decidable (r a b)

@[reducible]
def decidable_eq (A : Type u) :=
decidable_rel (@eq A)

inductive option (A : Type u)
| none {} : option
| some    : A → option

export option (none some)
export bool (ff tt)

inductive list (T : Type u)
| nil {} : list
| cons   : T → list → list

inductive nat
| zero : nat
| succ : nat → nat

/- Declare builtin and reserved notation -/

class has_zero     (A : Type u) := (zero : A)
class has_one      (A : Type u) := (one : A)
class has_add      (A : Type u) := (add : A → A → A)
class has_mul      (A : Type u) := (mul : A → A → A)
class has_inv      (A : Type u) := (inv : A → A)
class has_neg      (A : Type u) := (neg : A → A)
class has_sub      (A : Type u) := (sub : A → A → A)
class has_div      (A : Type u) := (div : A → A → A)
class has_dvd      (A : Type u) := (dvd : A → A → Prop)
class has_mod      (A : Type u) := (mod : A → A → A)
class has_le       (A : Type u) := (le : A → A → Prop)
class has_lt       (A : Type u) := (lt : A → A → Prop)
class has_append   (A : Type u) := (append : A → A → A)
class has_andthen  (A : Type u) := (andthen : A → A → A)
class has_union    (A : Type u) := (union : A → A → A)
class has_inter    (A : Type u) := (inter : A → A → A)
class has_sdiff    (A : Type u) := (sdiff : A → A → A)
class has_subset   (A : Type u) := (subset : A → A → Prop)
class has_ssubset  (A : Type u) := (ssubset : A → A → Prop)
/- Type classes has_emptyc and has_insert are
   used to implement polymorphic notation for collections.
   Example: {a, b, c}. -/
class has_emptyc   (A : Type u) := (emptyc : A)
class has_insert   (A : Type u) (C : Type u → Type v) := (insert : A → C A → C A)
/- Type class used to implement the notation { a ∈ c | p a } -/
class has_sep (A : Type u) (C : Type u → Type v) :=
(sep : (A → Prop) → C A → C A)
/- Type class for set-like membership -/
class has_mem (A : Type u) (C : Type u → Type v) := (mem : A → C A → Prop)

def zero     {A : Type u} [has_zero A]     : A            := has_zero.zero A
def one      {A : Type u} [has_one A]      : A            := has_one.one A
def add      {A : Type u} [has_add A]      : A → A → A    := has_add.add
def mul      {A : Type u} [has_mul A]      : A → A → A    := has_mul.mul
def sub      {A : Type u} [has_sub A]      : A → A → A    := has_sub.sub
def div      {A : Type u} [has_div A]      : A → A → A    := has_div.div
def dvd      {A : Type u} [has_dvd A]      : A → A → Prop := has_dvd.dvd
def mod      {A : Type u} [has_mod A]      : A → A → A    := has_mod.mod
def neg      {A : Type u} [has_neg A]      : A → A        := has_neg.neg
def inv      {A : Type u} [has_inv A]      : A → A        := has_inv.inv
def le       {A : Type u} [has_le A]       : A → A → Prop := has_le.le
def lt       {A : Type u} [has_lt A]       : A → A → Prop := has_lt.lt
def append   {A : Type u} [has_append A]   : A → A → A    := has_append.append
def andthen  {A : Type u} [has_andthen A]  : A → A → A    := has_andthen.andthen
def union    {A : Type u} [has_union A]    : A → A → A    := has_union.union
def inter    {A : Type u} [has_inter A]    : A → A → A    := has_inter.inter
def sdiff    {A : Type u} [has_sdiff A]    : A → A → A    := has_sdiff.sdiff
def subset   {A : Type u} [has_subset A]   : A → A → Prop := has_subset.subset
def ssubset  {A : Type u} [has_ssubset A]  : A → A → Prop := has_ssubset.ssubset
@[reducible]
def ge {A : Type u} [has_le A] (a b : A) : Prop := le b a
@[reducible]
def gt {A : Type u} [has_lt A] (a b : A) : Prop := lt b a
@[reducible]
def superset {A : Type u} [has_subset A] (a b : A) : Prop := subset b a
@[reducible]
def ssuperset {A : Type u} [has_ssubset A] (a b : A) : Prop := ssubset b a
def bit0 {A : Type u} [s  : has_add A] (a  : A)                 : A := add a a
def bit1 {A : Type u} [s₁ : has_one A] [s₂ : has_add A] (a : A) : A := add (bit0 a) one

attribute [pattern] zero one bit0 bit1 add

def insert {A : Type u} {C : Type u → Type v} [has_insert A C] : A → C A → C A :=
has_insert.insert

/- The empty collection -/
def emptyc {A : Type u} [has_emptyc A] : A :=
has_emptyc.emptyc A

def singleton {A : Type u} {C : Type u → Type v} [has_emptyc (C A)] [has_insert A C] (a : A) : C A :=
insert a emptyc

def sep {A : Type u} {C : Type u → Type v} [has_sep A C] : (A → Prop) → C A → C A :=
has_sep.sep

def mem {A : Type u} {C : Type u → Type v} [has_mem A C] : A → C A → Prop :=
has_mem.mem

/- num, pos_num instances -/

instance : has_zero num :=
⟨num.zero⟩

instance : has_one num :=
⟨num.pos pos_num.one⟩

instance : has_one pos_num :=
⟨pos_num.one⟩

namespace pos_num
  def is_one (a : pos_num) : bool :=
  pos_num.rec_on a tt (λ n r, ff) (λ n r, ff)

  def pred (a : pos_num) : pos_num :=
  pos_num.rec_on a one (λ n r, bit0 n) (λ n r, bool.rec_on (is_one n) (bit1 r) one)

  def size (a : pos_num) : pos_num :=
  pos_num.rec_on a one (λ n r, succ r) (λ n r, succ r)

  def add (a b : pos_num) : pos_num :=
  pos_num.rec_on a
    succ
    (λ n f b, pos_num.rec_on b
      (succ (bit1 n))
      (λ m r, succ (bit1 (f m)))
      (λ m r, bit1 (f m)))
    (λ n f b, pos_num.rec_on b
      (bit1 n)
      (λ m r, bit1 (f m))
      (λ m r, bit0 (f m)))
    b
end pos_num

instance : has_add pos_num :=
⟨pos_num.add⟩

namespace num
  open pos_num

  def add (a b : num) : num :=
  num.rec_on a b (λ pa, num.rec_on b (pos pa) (λ pb, pos (pos_num.add pa pb)))
end num

instance : has_add num :=
⟨num.add⟩

def std.priority.default : num := 1000
def std.priority.max     : num := 4294967295

/- nat basic instances -/

namespace nat
  protected def prio := num.add std.priority.default 100

  protected def add (a b : nat) : nat :=
  nat.rec a (λ b₁ r, nat.succ r) b

  def of_pos_num (p : pos_num) : nat :=
  pos_num.rec (succ zero) (λ n r, nat.add (nat.add r r) (succ zero)) (λ n r, nat.add r r) p

  def of_num (n : num) : nat :=
  num.rec zero (λ p, of_pos_num p) n
end nat

instance : has_zero nat := ⟨nat.zero⟩

instance : has_one nat := ⟨nat.succ (nat.zero)⟩

instance : has_add nat := ⟨nat.add⟩

/-
  Global declarations of right binding strength

  If a module reassigns these, it will be incompatible with other modules that adhere to these
  conventions.

  When hovering over a symbol, use "C-c C-k" to see how to input it.
-/
def std.prec.max   : num := 1024 -- the strength of application, identifiers, (, [, etc.
def std.prec.arrow : num := 25

/-
The next def is "max + 10". It can be used e.g. for postfix operations that should
be stronger than application.
-/

def std.prec.max_plus :=
num.succ (num.succ (num.succ (num.succ (num.succ (num.succ (num.succ (num.succ (num.succ
  (num.succ std.prec.max)))))))))

reserve postfix `⁻¹`:std.prec.max_plus  -- input with \sy or \-1 or \inv

infix =        := eq
infix ∈        := mem
notation a ∉ s := ¬ mem a s
infix +        := add
infix *        := mul
infix -        := sub
infix /        := div
infix ∣        := dvd
infix %        := mod
prefix -       := neg
postfix ⁻¹     := inv
infix <=       := le
infix >=       := ge
infix ≤        := le
infix ≥        := ge
infix <        := lt
infix >        := gt
infix ++       := append
infix ;        := andthen
notation `∅`   := emptyc
infix ∪        := union
infix ∩        := inter
infix ⊆        := subset
infix ⊇        := superset
infix ⊂        := ssubset
infix ⊃        := ssuperset
infix \        := sdiff

/- eq basic support -/

@[pattern] def rfl {A : Type u} {a : A} : a = a := eq.refl a

namespace eq
  variables {A : Type u}
  variables {a b c a': A}

  attribute [elab_as_eliminator]
  theorem subst {P : A → Prop} (H₁ : a = b) (H₂ : P a) : P b :=
  eq.rec H₂ H₁

  theorem trans (H₁ : a = b) (H₂ : b = c) : a = c :=
  subst H₂ H₁

  theorem symm : a = b → b = a :=
  λ h, eq.rec (refl a) h
end eq

notation H1 ▸ H2 := eq.subst H1 H2

attribute [subst] eq.subst
attribute [refl] eq.refl
attribute [trans] eq.trans
attribute [symm] eq.symm

/- sizeof -/

class has_sizeof (A : Type u) :=
(sizeof : A → nat)

def sizeof {A : Type u} [s : has_sizeof A] : A → nat :=
has_sizeof.sizeof

/-
Declare sizeof instances and lemmas for types declared before has_sizeof.
From now on, the inductive compiler will automatically generate sizeof instances and lemmas.
-/

/- Every type `A` has a default has_sizeof instance that just returns 0 for every element of `A` -/
instance default_has_sizeof (A : Type u) : has_sizeof A :=
⟨λ a, nat.zero⟩

attribute [simp, defeq, simp.sizeof]
def default_has_sizeof_eq (A : Type u) (a : A) : @sizeof A (default_has_sizeof A) a = 0 :=
rfl

instance : has_sizeof nat := ⟨λ a, a⟩

attribute [simp, defeq, simp.sizeof]
def sizeof_nat_eq (a : nat) : sizeof a = a :=
rfl

instance (A : Type u) (B : Type v) [has_sizeof A] [has_sizeof B] : has_sizeof (prod A B) :=
⟨λ p, prod.cases_on p (λ a b, 1 + sizeof a + sizeof b)⟩

attribute [simp, defeq, simp.sizeof]
def sizeof_prod_eq {A : Type u} {B : Type v} [has_sizeof A] [has_sizeof B] (a : A) (b : B) : sizeof (prod.mk a b) = 1 + sizeof a + sizeof b :=
rfl

instance (A : Type u) (B : Type v) [has_sizeof A] [has_sizeof B] : has_sizeof (sum A B) :=
⟨λ s, sum.cases_on s (λ a, 1 + sizeof a) (λ b, 1 + sizeof b)⟩

attribute [simp, defeq, simp.sizeof]
def sizeof_sum_eq_left {A : Type u} {B : Type v} [has_sizeof A] [has_sizeof B] (a : A) : sizeof (@sum.inl A B a) = 1 + sizeof a :=
rfl

attribute [simp, defeq, simp.sizeof]
def sizeof_sum_eq_right {A : Type u} {B : Type v} [has_sizeof A] [has_sizeof B] (b : B) : sizeof (@sum.inr A B b) = 1 + sizeof b :=
rfl

instance (A : Type u) (B : A → Type v) [has_sizeof A] [∀ a, has_sizeof (B a)] : has_sizeof (sigma B) :=
⟨λ p, sigma.cases_on p (λ a b, 1 + sizeof a + sizeof b)⟩

attribute [simp, defeq, simp.sizeof]
def sizeof_sigma_eq {A : Type u} {B : A → Type v} [has_sizeof A] [∀ a, has_sizeof (B a)] (a : A) (b : B a) : sizeof (@sigma.mk A B a b) = 1 + sizeof a + sizeof b :=
rfl

instance : has_sizeof unit := ⟨λ u, 1⟩

attribute [simp, defeq, simp.sizeof]
def sizeof_unit_eq (u : unit) : sizeof u = 1 :=
rfl

instance : has_sizeof poly_unit := ⟨λ u, 1⟩

attribute [simp, defeq, simp.sizeof]
def sizeof_poly_unit_eq (u : poly_unit) : sizeof u = 1 :=
rfl

instance : has_sizeof bool := ⟨λ u, 1⟩

attribute [simp, defeq, simp.sizeof]
def sizeof_bool_eq (b : bool) : sizeof b = 1 :=
rfl

instance : has_sizeof pos_num := ⟨λ p, nat.of_pos_num p⟩

attribute [simp, defeq, simp.sizeof]
def sizeof_pos_num_eq (p : pos_num) : sizeof p = nat.of_pos_num p :=
rfl

instance : has_sizeof num := ⟨λ p, nat.of_num p⟩

attribute [simp, defeq, simp.sizeof]
def sizeof_num_eq (n : num) : sizeof n = nat.of_num n :=
rfl

instance (A : Type u) [has_sizeof A] : has_sizeof (option A) :=
⟨λ o, option.cases_on o 1 (λ a, 1 + sizeof a)⟩

attribute [simp, defeq, simp.sizeof]
def sizeof_option_none_eq (A : Type u) [has_sizeof A] : sizeof (@none A) = 1 :=
rfl

attribute [simp, defeq, simp.sizeof]
def sizeof_option_some_eq {A : Type u} [has_sizeof A] (a : A) : sizeof (some a) = 1 + sizeof a :=
rfl

instance (A : Type u) [has_sizeof A] : has_sizeof (list A) :=
⟨λ l, list.rec_on l 1 (λ a t ih, 1 + sizeof a + ih)⟩

attribute [simp, defeq, simp.sizeof]
def sizeof_list_nil_eq (A : Type u) [has_sizeof A] : sizeof (@list.nil A) = 1 :=
rfl

attribute [simp, defeq, simp.sizeof]
def sizeof_list_cons_eq {A : Type u} [has_sizeof A] (a : A) (l : list A) : sizeof (list.cons a l) = 1 + sizeof a + sizeof l :=
rfl

attribute [simp.sizeof]
lemma nat_add_zero (n : nat) : n + 0 = n := rfl
