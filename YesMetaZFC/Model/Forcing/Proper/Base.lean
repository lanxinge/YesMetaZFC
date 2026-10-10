import YesMetaZFC.Model.Forcing.Proper.Syntax
import YesMetaZFC.Model.Forcing.Proper.Elementary.Club

/-! # properness 的实际 club 见证与初等模型主条件

只在 B∪𝒫(B) 上固定一个真实的 proper club。任何包含该 club 的内部可数初等
N 都捕获其交集，故 N 中每个正条件都有 N 的主加强；不再需要另行选取 N。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}} (I : kpair_convention_l.Interpretation M)

def Pr_base_d (ω B R z X C : M.Domain) : Prop :=
  (∀ a, M.mem a X ↔ M.mem a B ∨ M.MemberSubset a B) ∧ Cc_club_d I ω X C ∧
    ∀ N, M.mem N C → ∀ p, M.mem p N → M.mem p B → p ≠ z →
      ∃ q, Below_d M B R z q p ∧ Mstr_d M B R z N q

def pr_base_m {n} (ω B R z X C : Term n) : Formula 1 n :=
  .conj (.forallE (.iff (.mem .newest X.weaken) (.disj (.mem .newest B.weaken) (Formula.subset .newest B.weaken))))
    (.conj (cc_club_m kpair_convention_l ω X C)
      (Formula.forallMem C (Formula.forallMem .newest
        (.imp (.mem .newest B.weaken.weaken)
          (.imp (.neg (Formula.extensionalEq .newest z.weaken.weaken)) (.existsE
            (.conj (below_m B.weaken.weaken.weaken R.weaken.weaken.weaken z.weaken.weaken.weaken .newest (.bound 1))
              (mstr_m B.weaken.weaken.weaken R.weaken.weaken.weaken z.weaken.weaken.weaken (.bound 2) .newest))))))))
derive_free_closed pr_base_m

theorem pr_base_sat_l (hE : Extensional M) {n} (ρ : Env M n) (ω B R z X C : Term n) :
    Formula.satisfies ρ (pr_base_m ω B R z X C) ↔
      Pr_base_d I (ω.eval ρ) (B.eval ρ) (R.eval ρ) (z.eval ρ) (X.eval ρ) (C.eval ρ) := by
  simp only [pr_base_m, Pr_base_d, Formula.satisfies_conj_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_iff_iff, Formula.satisfies_mem_iff, Formula.satisfies_disj_iff,
    Formula.satisfies_subset_iff, cc_club_sat_l I hE, Formula.satisfies_forallMem_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_neg_iff, Formula.satisfies_extensionalEq_iff_eq hE,
    Formula.satisfies_exists_iff, below_sat_l M hE, mstr_sat_l M hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

/-- 原 properness 自动产生供所有初等子模型共同使用的实际 club 见证。 -/
theorem pr_base_exists_l (hZF : M.Models ZF) {ω B R z} (h : Proper_d I ω B R z) :
    ∃ X C, Pr_base_d I ω B R z X C := by
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF B
  obtain ⟨X, hX⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) B P
  obtain ⟨C, hC, hc⟩ := h X (fun x hx => (hX x).mpr (Or.inl hx))
  exact ⟨X, C, fun x => (hX x).trans (or_congr Iff.rfl (hP x)), hC, hc⟩

variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "J" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))

omit I in
/-- 包含已构造 club 见证的同一个 N，可为其任意正条件选择主加强。 -/
theorem pr_base_master_l {ω χ H c T d N S B R z X C p} (hω : M.IsOmega ω)
    (hχ : M.IsRegularCardinal J χ) (hωχ : M.mem ω χ) (hH : H_d J χ H)
    (hM : Smem_d J c H T) (hS : Ssub_d J c d H T N S) (he : Selem_d J ω c d)
    (hωN : M.mem ω N) (hCN : M.mem C N) (hN : M.CardinalLessOrEqual J N ω)
    (h : Pr_base_d J ω B R z X C) (hpN : M.mem p N) (hpB : M.mem p B) (hz : p ≠ z) :
    ∃ q, Below_d M B R z q p ∧ Mstr_d M B R z N q := by
  obtain ⟨K, hK⟩ := KP.intersection_exists_d (ZF.modelsKP hZF) N X
  have hKC := selem_club_mem_l hZFC hω hχ hωχ hH hM hS he hωN hCN hN h.2.1 hK
  obtain ⟨q, hqp, hq⟩ := h.2.2 K hKC p ((hK p).mpr ⟨hpN, (h.1 p).mpr (Or.inl hpB)⟩) hpB hz
  refine ⟨q, hqp, hq.1, hq.2.1, fun D hDN hd r hr => ?_⟩
  have hDK := (hK D).mpr ⟨hDN, (h.1 D).mpr (Or.inr (fun a ha => (hd.1 a ha).1))⟩
  obtain ⟨s, hsD, hsK, hrs⟩ := hq.2.2 D hDK hd r hr
  exact ⟨s, hsD, ((hK s).mp hsK).1, hrs⟩

end YesMetaZFC.Model.Forcing.Internal
