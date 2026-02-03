def MyInt' : Type := Nat × Nat

def MyInt.eq (n k : MyInt') : Prop :=
  n.1 + k.2 = n.2 + k.1

def MyInt.eq.eqv : Equivalence MyInt.eq where
  refl := by unfold eq; intros; omega
  symm := by unfold eq; intros; omega
  trans := by unfold eq; intros; omega

instance : Setoid MyInt' where
  r := MyInt.eq
  iseqv := MyInt.eq.eqv

def MyInt := Quotient instSetoidMyInt'

def MyInt.mk (n : MyInt') : MyInt := Quotient.mk _ n

instance : OfNat MyInt n where
  ofNat := MyInt.mk (n, 0)

def MyInt.add' (n k : MyInt') : MyInt := .mk (n.1 + k.1, n.2 + k.2)

instance : Add MyInt where
  add (n : MyInt) := n.lift₂ MyInt.add' <| by
    intro a b a' b' heq heq'
    apply Quotient.sound
    cases a; cases b; cases a'; cases b'
    simp_all only [· ≈ ·, Setoid.r, MyInt.eq]
    omega

-- (a, b) * (c, d) = (ac + bd, ad + bc)
def MyInt.mul' (n k : MyInt') : MyInt := .mk (n.1 * k.1 + n.2 * k.2, n.1 * k.2 + n.2 * k.1)

-- instance : Mul MyInt where
--   mul (n : MyInt) := n.lift₂ MyInt.mul' <| by
--     intro a b a' b' heq heq'
--     apply Quotient.sound
--     cases a; cases b; cases a'; cases b'
--     simp_all only [· ≈ ·, Setoid.r, MyInt.eq]
--     omega
