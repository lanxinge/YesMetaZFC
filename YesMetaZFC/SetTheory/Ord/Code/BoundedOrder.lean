import YesMetaZFC.SetTheory.Ord.Code.Pair
import YesMetaZFC.SetTheory.KP.Kuratowski

/-! # 规范序数方块及其比较的有界检查

方块用双向有界配对覆盖刻画。比较的六个坐标全部界于原方块边长；
最大值是原坐标之一，因此这些界不删掉任何合法比较。
-/
namespace YesMetaZFC.SetTheory
open Definitional.Project
universe u
variable {M : Structure.{u}}

def Oc_grid_d (t X : M.Domain) : Prop :=
  (∀ p, M.mem p X → ∃ a, M.mem a t ∧ ∃ b, M.mem b t ∧ KPair_d M p a b) ∧
    ∀ a, M.mem a t → ∀ b, M.mem b t → ∃ p, M.mem p X ∧ KPair_d M p a b

def oc_grid_m {d} (t X : Term d) : Formula 1 d := set[d] ⟪
  (∀ p ∈ ⌜X⌝ₛ, ∃ a ∈ ⌜t⌝ₛ, ∃ b ∈ ⌜t⌝ₛ, ⌜kpair0_m⌝ₚ(p,a,b)) ∧
    (∀ a ∈ ⌜t⌝ₛ, ∀ b ∈ ⌜t⌝ₛ, ∃ p ∈ ⌜X⌝ₛ, ⌜kpair0_m⌝ₚ(p,a,b))⟫
derive_free_closed oc_grid_m

theorem oc_grid_delta_l {d} (t X : Term d) : (oc_grid_m t X).IsDelta0 :=
  .conj (.forallMem _ (.existsMem _ (.existsMem _ (kpair0_delta_l ..))))
    (.forallMem _ (.forallMem _ (.existsMem _ (kpair0_delta_l ..))))

theorem oc_grid_sat_l (hE : Extensional M) {d} (ρ : Env M d) (t X : Term d) :
    Formula.satisfies ρ (oc_grid_m t X) ↔ Oc_grid_d (t.eval ρ) (X.eval ρ) := by
  simp only [oc_grid_m,Oc_grid_d,Formula.satisfies_conj_iff,Formula.satisfies_forallMem_iff,
    Formula.satisfies_existsMem_iff,kpair0_sat_l hE,Definitional.Term.eval_weaken,Definitional.Term.eval_newest]

theorem oc_grid_read_l (hE : Extensional M) (hP : ∀ a b, ∃ p, Pair_d M p a b) {t X : M.Domain} :
    Oc_grid_d t X ↔ M.IsCartesianProduct (kpair_interpretation_l M hE hP) X t t := by
  constructor
  · intro h p
    exact ⟨h.1 p,fun ⟨a,ha,b,hb,pair⟩ => by
      obtain ⟨q,hq,code⟩ := h.2 a ha b hb
      exact (kpair_unique_l M hE code pair) ▸ hq⟩
  · intro h
    refine ⟨fun p hp => (h p).mp hp,fun a ha b hb => ?_⟩
    obtain ⟨p,pair⟩ := (kpair_interpretation_l M hE hP).total a b
    exact ⟨p,(h p).mpr ⟨a,ha,b,hb,pair⟩,pair⟩

def Oc_less_d (t p q : M.Domain) : Prop :=
  ∃ a, M.mem a t ∧ ∃ b, M.mem b t ∧ ∃ c, M.mem c t ∧ ∃ d, M.mem d t ∧
    ∃ m, M.mem m t ∧ ∃ n, M.mem n t ∧ KPair_d M p a b ∧ KPair_d M q c d ∧
      M.IsOrdinalMaximum a b m ∧ M.IsOrdinalMaximum c d n ∧
      (M.mem m n ∨ m = n ∧ (M.mem a c ∨ a = c ∧ M.mem b d))

def oc_less_m {d} (t p q : Term d) : Formula 1 d := set[d] ⟪
  ∃ a ∈ ⌜t⌝ₛ, ∃ b ∈ ⌜t⌝ₛ, ∃ c ∈ ⌜t⌝ₛ, ∃ d ∈ ⌜t⌝ₛ, ∃ m ∈ ⌜t⌝ₛ, ∃ n ∈ ⌜t⌝ₛ,
    ⌜kpair0_m⌝ₚ(⌜p⌝ₛ,a,b) ∧ ⌜kpair0_m⌝ₚ(⌜q⌝ₛ,c,d) ∧
    ⌜Formula.isOrdinalMaximum⌝ₚ(a,b,m) ∧ ⌜Formula.isOrdinalMaximum⌝ₚ(c,d,n) ∧
    (m ∈ n ∨ m = n ∧ (a ∈ c ∨ a = c ∧ b ∈ d))⟫
derive_free_closed oc_less_m

theorem oc_less_delta_l {d} (t p q : Term d) : (oc_less_m t p q).IsDelta0 := by
  have max {n} (a b m : Term n) : (Formula.isOrdinalMaximum a b m).IsDelta0 :=
    .disj (.conj (.atom _ _ _) (.disj (.atom _ _ _) (.mem _ _))) (.conj (.atom _ _ _) (.mem _ _))
  exact .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _
    (.conj (kpair0_delta_l ..) (.conj (kpair0_delta_l ..) (.conj (max ..) (.conj (max ..)
      (.disj (.mem _ _) (.conj (.atom _ _ _) (.disj (.mem _ _) (.conj (.atom _ _ _) (.mem _ _))))))))))))))

theorem oc_less_sat_l (hE : Extensional M) {d} (ρ : Env M d) (t p q : Term d) :
    Formula.satisfies ρ (oc_less_m t p q) ↔ Oc_less_d (t.eval ρ) (p.eval ρ) (q.eval ρ) := by
  simp only [oc_less_m,Oc_less_d,Formula.satisfies_existsMem_iff,Formula.satisfies_conj_iff,
    kpair0_sat_l hE,Formula.satisfies_isOrdinalMaximum_iff hE,Formula.satisfies_disj_iff,
    Formula.satisfies_mem_iff,Formula.satisfies_extensionalEq_iff_eq hE,
    Definitional.Term.eval_weaken,Definitional.Term.eval_newest]

theorem oc_less_read_l (hE : Extensional M) (hP : ∀ a b, ∃ p, Pair_d M p a b) {t X p q : M.Domain}
    (grid : Oc_grid_d t X) (hp : M.mem p X) (hq : M.mem q X) :
    Oc_less_d t p q ↔ M.CanonicalOrdinalPairLess (kpair_interpretation_l M hE hP) p q := by
  constructor
  · rintro ⟨a,_,b,_,c,_,d,_,m,_,n,_,pa,qb,am,bn,lt⟩
    exact ⟨a,b,c,d,m,n,pa,qb,am,bn,lt⟩
  · rintro ⟨a,b,c,d,m,n,pa,qb,am,bn,lt⟩
    obtain ⟨a',ha,b',hb,pa'⟩ := grid.1 p hp
    obtain ⟨c',hc,d',hd,qb'⟩ := grid.1 q hq
    obtain ⟨ea,eb⟩ := kpair_injective_l M pa' pa
    obtain ⟨ec,ed⟩ := kpair_injective_l M qb' qb
    subst a' b' c' d'
    exact ⟨a,ha,b,hb,c,hc,d,hd,m,am.mem ha hb,n,bn.mem hc hd,pa,qb,am,bn,lt⟩

end YesMetaZFC.SetTheory
