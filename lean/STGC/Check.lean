/-
  Cross-check of the definitions in Defs.lean against the computational tools (task item 3).
  Not part of the proof: `#eval` only.
-/
import STGC.Defs

namespace STGC.Check
open STGC

/-- The word whose bits, most significant first (position 0), are the binary digits of `t`. -/
def ofNat (n t : ℕ) : Word n := fun i => t.testBit (n - 1 - i.val)

/-- The word in position `t` of the binary reflected Gray code. -/
def grayWord (n t : ℕ) : Word n := ofNat n (t ^^^ (t >>> 1))

def isConstB (n : ℕ) [NeZero n] (w : Word n) : Bool := (List.range n).all fun i => w (i : ZMod n) == w 0

def isFirstOccB (n : ℕ) [NeZero n] (w : Word n) : Bool :=
  !isConstB n w && (List.range n).all fun k => rank w ≤ rank (rot (k : ZMod n) w)

def adjB (n : ℕ) [NeZero n] (u v : Word n) : Bool :=
  (List.range n).any fun k => hammingDist u (rot (k : ZMod n) v) == 1

def toStr (n : ℕ) (w : Word n) : String := String.mk ((List.range n).map fun i => if w (i : ZMod n) then '1' else '0')

/-- `rank (grayWord n t) = t` for all `t < 2^n`: the rank is the position in the reflected Gray code. -/
def rankGrayOK (n : ℕ) [NeZero n] : Bool := (List.range (2 ^ n)).all fun t => rank (grayWord n t) == t

/-- The Degni–Drisko list (first occurrences in rank order) and the DD property, computed from the definitions. -/
def ddList (n : ℕ) [NeZero n] : List (Word n) :=
  ((List.range (2 ^ n)).map (grayWord n)).filter (isFirstOccB n)

def ddHolds (n : ℕ) [NeZero n] : Bool :=
  let l := ddList n
  (l.zip l.tail).all fun (u, v) => adjB n u v

#eval (rankGrayOK 5, rankGrayOK 7, rankGrayOK 9)
#eval ((ddList 7).map (toStr 7))
#eval (ddList 5).length
#eval (ddList 7).length
#eval (ddList 11).length
#eval (ddHolds 5, ddHolds 7, ddHolds 9, ddHolds 11)

end STGC.Check
