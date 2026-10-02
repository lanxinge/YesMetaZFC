import YesMetaZFC.SetTheory.Descriptive.Projection

/-! # 内部子空间的迹与点类集合

交集、相对补和点类取迹均用模型内部的实际集合表示，供解析和射影层共同使用。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}}

def Tr_d (X K L : M.Domain) : Prop := ∀ x, M.mem x L ↔ M.mem x X ∧ M.mem x K
def tr_m {d} (X K L : Term d) : Formula 1 d := Formula.isIntersection L X K
derive_free_closed tr_m
theorem tr_sat_l {d} (ρ : Env M d) (X K L : Term d) :
    Formula.satisfies ρ (tr_m X K L) ↔ Tr_d (M := M) (X.eval ρ) (K.eval ρ) (L.eval ρ) := by
  simp only [tr_m, Formula.isIntersection, Tr_d, Formula.satisfies_forall_iff,
    Formula.satisfies_iff_iff, Formula.satisfies_mem_iff, Formula.satisfies_conj_iff,
    Definitional.Term.eval_weaken]; rfl
theorem tr_exists_l (hKP : M.Models KP) (X K : M.Domain) : ∃ L, Tr_d X K L := KP.intersection_exists_d hKP X K
theorem tr_unique_l (hE : Extensional M) {X K L U : M.Domain} (h : Tr_d X K L) (k : Tr_d X K U) : L = U :=
  hE.eq_of_same_members L U (fun x => (h x).trans (k x).symm)

theorem tr_compl_l {B X K L U V : M.Domain} (hX : M.MemberSubset X B) (h : Cm_d B K L)
    (hU : Tr_d X K U) (hV : Tr_d X L V) : Cm_d X U V := by
  intro x
  refine (hV x).trans (and_congr_right fun hx => ?_)
  exact ((h x).trans ⟨And.right, fun hn => ⟨hX x hx, hn⟩⟩).trans
    (not_congr ((hU x).trans ⟨And.right, fun hk => ⟨hx, hk⟩⟩)).symm

def Rclass_d (X C K : M.Domain) : Prop := ∃ L, M.mem L C ∧ Tr_d X L K
def rclass_m {d} (X C K : Term d) : Formula 1 d := Formula.existsMem C (tr_m X.weaken .newest K.weaken)
derive_free_closed rclass_m
@[prove_auto_norm semantic]
theorem rclass_sat_l {d} (ρ : Env M d) (X C K : Term d) :
    Formula.satisfies ρ (rclass_m X C K) ↔ Rclass_d (M := M) (X.eval ρ) (C.eval ρ) (K.eval ρ) := by
  simp only [rclass_m, Rclass_d, Formula.satisfies_existsMem_iff, tr_sat_l, Definitional.Term.eval_weaken]; rfl

theorem rclass_collection_l (hZF : M.Models ZF) (X C : M.Domain) : ∃ D, ∀ K, M.mem K D ↔ Rclass_d X C K := by
  let ρ : Env M 1 := ⟨fun _ => X, fun _ => X⟩
  let φ : BinarySchema 1 := { body := tr_m (.bound 2) (.bound 1) .newest }
  have hp K L : φ.denote ρ K L ↔ Tr_d X K L := tr_sat_l _ _ _ _
  obtain ⟨D, hD⟩ := ZF.exists_functionalImageOn hZF φ ρ C
    (fun K _ => (tr_exists_l (ZF.modelsKP hZF) X K).imp fun L h => (hp K L).mpr h)
    (fun K _ L U h k => tr_unique_l hZF.1 ((hp K L).mp h) ((hp K U).mp k))
  exact ⟨D, fun K => (hD K).trans (exists_congr fun L => and_congr_right fun _ => hp L K)⟩

end YesMetaZFC.SetTheory.Descriptive
