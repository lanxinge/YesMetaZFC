import YesMetaZFC.SetTheory.Kuratowski

/-! # Jensen 有限基及保持传递性的一步运算

前九项按 Jensen《Basic Fine Structure Theory》定理 2.2.15 排列；后四项是
引理 2.3.2 的辅助运算。三元组固定为 (x,(y,z))，F₆ 读取第二坐标。
编号只是固定有限菜单；闭包长度不使用宿主 Nat，而由模型内部递归处理。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

inductive Rd_sym where
  | pair | diff | prod | mid | last | union | range | mem | fibers
  | opair | triple | adj | fiber
  deriving DecidableEq

def Rd_entry_d (x y R : M.Domain) : Prop := ∃ p, KPair_d M p x y ∧ M.mem p R

def rd_entry_m {n} (x y R : Term n) : Formula 1 n :=
  Formula.orderedPairMem kpair_convention_l x y R
derive_free_closed rd_entry_m

theorem rd_entry_sat_l (hE : Extensional M) {n} (ρ : Env M n) (x y R : Term n) :
    Formula.satisfies ρ (rd_entry_m x y R) ↔ Rd_entry_d (x.eval ρ) (y.eval ρ) (R.eval ρ) := by
  simp only [rd_entry_m, Formula.orderedPairMem, kpair_convention_l, Rd_entry_d, Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff, kpair_sat_l M hE, Formula.satisfies_mem_iff,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

def Rd_triple_d (p x y z : M.Domain) : Prop := ∃ q, KPair_d M q y z ∧ KPair_d M p x q

def rd_triple_m {n} (p x y z : Term n) : Formula 1 n :=
  .existsE (.conj (kpair_m .newest y.weaken z.weaken) (kpair_m p.weaken x.weaken .newest))
derive_free_closed rd_triple_m

theorem rd_triple_sat_l (hE : Extensional M) {n} (ρ : Env M n) (p x y z : Term n) :
    Formula.satisfies ρ (rd_triple_m p x y z) ↔ Rd_triple_d (p.eval ρ) (x.eval ρ) (y.eval ρ) (z.eval ρ) := by
  simp only [rd_triple_m, Rd_triple_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    kpair_sat_l M hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

def Rd_fiber_d (R y D : M.Domain) : Prop := ∀ x, M.mem x D ↔ Rd_entry_d x y R

def rd_fiber_m {n} (R y D : Term n) : Formula 1 n :=
  .forallE (.iff (.mem .newest D.weaken) (rd_entry_m .newest y.weaken R.weaken))
derive_free_closed rd_fiber_m

theorem rd_fiber_sat_l (hE : Extensional M) {n} (ρ : Env M n) (R y D : Term n) :
    Formula.satisfies ρ (rd_fiber_m R y D) ↔ Rd_fiber_d (R.eval ρ) (y.eval ρ) (D.eval ρ) := by
  simp only [rd_fiber_m, Rd_fiber_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, rd_entry_sat_l hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

def Rd_mem_d : Rd_sym → M.Domain → M.Domain → M.Domain → M.Domain → Prop
  | .pair, x, y, _, t => t = x ∨ t = y
  | .diff, x, y, _, t => M.mem t x ∧ ¬ M.mem t y
  | .prod, x, y, _, t => ∃ a b, M.mem a x ∧ M.mem b y ∧ KPair_d M t a b
  | .mid, x, y, _, t => ∃ a b c, M.mem b x ∧ Rd_entry_d a c y ∧ Rd_triple_d t a b c
  | .last, x, y, _, t => ∃ a b c, M.mem c x ∧ Rd_entry_d a b y ∧ Rd_triple_d t a b c
  | .union, x, _, _, t => ∃ a, M.mem a x ∧ M.mem t a
  | .range, x, _, _, t => ∃ a, Rd_entry_d a t x
  | .mem, x, _, _, t => ∃ a b, M.mem a x ∧ M.mem b x ∧ M.mem a b ∧ KPair_d M t a b
  | .fibers, x, y, _, t => ∃ b, M.mem b y ∧ Rd_fiber_d x b t
  | .opair, x, y, _, t => M.IsSingletonOf t x ∨ Pair_d M t x y
  | .triple, x, y, z, t => M.IsSingletonOf t x ∨ ∃ p, KPair_d M p y z ∧ Pair_d M t x p
  | .adj, x, y, z, t => t = x ∨ KPair_d M t y z
  | .fiber, x, y, _, t => Rd_entry_d t y x

def rd_mem_m {n} : Rd_sym → Term n → Term n → Term n → Term n → Formula 1 n
  | .pair, x, y, _, t => .disj (Formula.extensionalEq t x) (Formula.extensionalEq t y)
  | .diff, x, y, _, t => .conj (.mem t x) (.neg (.mem t y))
  | .prod, x, y, _, t => .existsE (.existsE (.conj (.mem (.bound 1) x.weaken.weaken)
      (.conj (.mem .newest y.weaken.weaken) (kpair_m t.weaken.weaken (.bound 1) .newest))))
  | .mid, x, y, _, t => .existsE (.existsE (.existsE (.conj (.mem (.bound 1) x.weaken.weaken.weaken)
      (.conj (rd_entry_m (.bound 2) .newest y.weaken.weaken.weaken)
        (rd_triple_m t.weaken.weaken.weaken (.bound 2) (.bound 1) .newest)))))
  | .last, x, y, _, t => .existsE (.existsE (.existsE (.conj (.mem .newest x.weaken.weaken.weaken)
      (.conj (rd_entry_m (.bound 2) (.bound 1) y.weaken.weaken.weaken)
        (rd_triple_m t.weaken.weaken.weaken (.bound 2) (.bound 1) .newest)))))
  | .union, x, _, _, t => Formula.existsMem x (.mem t.weaken .newest)
  | .range, x, _, _, t => .existsE (rd_entry_m .newest t.weaken x.weaken)
  | .mem, x, _, _, t => .existsE (.existsE (.conj (.mem (.bound 1) x.weaken.weaken)
      (.conj (.mem .newest x.weaken.weaken) (.conj (.mem (.bound 1) .newest)
        (kpair_m t.weaken.weaken (.bound 1) .newest)))))
  | .fibers, x, y, _, t => Formula.existsMem y (rd_fiber_m x.weaken .newest t.weaken)
  | .opair, x, y, _, t => .disj (Formula.isSingleton t x) (Formula.isUnorderedPair t x y)
  | .triple, x, y, z, t => .disj (Formula.isSingleton t x)
      (.existsE (.conj (kpair_m .newest y.weaken z.weaken) (Formula.isUnorderedPair t.weaken x.weaken .newest)))
  | .adj, x, y, z, t => .disj (Formula.extensionalEq t x) (kpair_m t y z)
  | .fiber, x, y, _, t => rd_entry_m t y x

@[simp] theorem rd_mem_closed_l {n} (k : Rd_sym) (x y z t : Term n)
    (hx : x.freeSupport = []) (hy : y.freeSupport = []) (hz : z.freeSupport = []) (ht : t.freeSupport = []) :
    (rd_mem_m k x y z t).FreeClosed := by
  cases k <;> simp -implicitDefEqProofs [rd_mem_m, Definitional.Formula.FreeClosed, hx, hy, hz, ht]

theorem rd_mem_sat_l (hE : Extensional M) {n} (ρ : Env M n) (k : Rd_sym) (x y z t : Term n) :
    Formula.satisfies ρ (rd_mem_m k x y z t) ↔ Rd_mem_d k (x.eval ρ) (y.eval ρ) (z.eval ρ) (t.eval ρ) := by
  cases k <;> simp only [rd_mem_m, Rd_mem_d, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_neg_iff, Formula.satisfies_exists_iff, Formula.satisfies_existsMem_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_extensionalEq_iff_eq hE, Formula.satisfies_isSingleton_iff hE,
    pair_sat_l M hE, kpair_sat_l M hE, rd_entry_sat_l hE, rd_triple_sat_l hE, rd_fiber_sat_l hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest] <;> rfl

/-- 所有运算均以唯一输出关系呈现，不选择模型中的集合对象。 -/
def Rd_fun_d (k : Rd_sym) (x y z w : M.Domain) : Prop := ∀ t, M.mem t w ↔ Rd_mem_d k x y z t

def rd_fun_m {n} (k : Rd_sym) (x y z w : Term n) : Formula 1 n :=
  .forallE (.iff (.mem .newest w.weaken) (rd_mem_m k x.weaken y.weaken z.weaken .newest))
derive_free_closed rd_fun_m

theorem rd_fun_sat_l (hE : Extensional M) {n} (ρ : Env M n) (k : Rd_sym) (x y z w : Term n) :
    Formula.satisfies ρ (rd_fun_m k x y z w) ↔ Rd_fun_d k (x.eval ρ) (y.eval ρ) (z.eval ρ) (w.eval ρ) := by
  simp only [rd_fun_m, Rd_fun_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, rd_mem_sat_l hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

theorem rd_fun_unique_l (hE : Extensional M) {k : Rd_sym} {x y z v w : M.Domain}
    (hv : Rd_fun_d k x y z v) (hw : Rd_fun_d k x y z w) : v = w :=
  hE.eq_of_same_members v w (fun t => (hv t).trans (hw t).symm)

end YesMetaZFC.SetTheory.InnerModel
