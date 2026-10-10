import YesMetaZFC.Model.SetTheory.Internal.SourceBranch
import YesMetaZFC.Model.SetTheory.Internal.Sigma1Substructure
import YesMetaZFC.Model.SetTheory.Internal.EmbeddingOmega
import YesMetaZFC.SetTheory.InnerModel.Order.Coordinates

/-! # 枝反射的可定义良基关系

把模型内没有下降枝的每个关系加上固定标签。标签包含载体、关系和当前点，
原二元公式由此同时处理所有源内关系，供超幂的共同纤维论证使用。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Sb_chain_d (ω A R f : M.Domain) : Prop := Fn0_d ω A f ∧ Wf_desc_d R f

def sb_chain_m {n} (ω A R f : Term n) : Formula 1 n := .conj (fn0_m ω A f)
  (Formula.forallMem ω (Formula.forallMem ω.weaken (Formula.forallMem A.weaken.weaken
    (Formula.forallMem A.weaken.weaken.weaken (.imp (KP.succ0_m (.bound 2) (.bound 3))
      (.imp (rd_entry0_m (.bound 3) (.bound 1) f.weaken.weaken.weaken.weaken)
        (.imp (rd_entry0_m (.bound 2) .newest f.weaken.weaken.weaken.weaken)
          (rd_entry0_m .newest (.bound 1) R.weaken.weaken.weaken.weaken))))))))
derive_free_closed sb_chain_m

theorem sb_chain_delta_l {n} (ω A R f : Term n) : (sb_chain_m ω A R f).IsDelta0 :=
  .conj (fn0_delta_l ..) (.forallMem _ (.forallMem _ (.forallMem _ (.forallMem _
    (.imp (KP.succ0_delta_l ..) (.imp (rd_entry0_delta_l ..) (.imp (rd_entry0_delta_l ..) (rd_entry0_delta_l ..))))))))

theorem sb_chain_sat_l (hE : Extensional M) {n} (ρ : Env M n) (ω A R f : Term n) :
    Formula.satisfies ρ (sb_chain_m ω A R f) ↔ Sb_chain_d (ω.eval ρ) (A.eval ρ) (R.eval ρ) (f.eval ρ) := by
  simp only [sb_chain_m, Formula.satisfies_conj_iff, fn0_sat_l hE, Formula.satisfies_forallMem_iff,
    Formula.satisfies_imp_iff, KP.succ0_sat_l hE, rd_entry0_sat_l hE, Definitional.Term.eval_weaken]
  exact ⟨fun ⟨hf, h⟩ => ⟨hf, fun i j x y hs hx hy => h i (hf.bound_l hx).1 j (hf.bound_l hy).1
    x (hf.bound_l hx).2 y (hf.bound_l hy).2 hs hx hy⟩,
    fun ⟨hf, hd⟩ => ⟨hf, fun i _ j _ x _ y _ => hd i j x y⟩⟩

def Sb_edge_d (A R u v : M.Domain) : Prop := ∃ x, M.mem x A ∧ ∃ y, M.mem y A ∧
  Rd_triple_d u A R x ∧ Rd_triple_d v A R y ∧ Rd_entry_d x y R

def sb_edge_m {n} (ω A R u v : Term n) : Formula 1 n := .conj (omega0_m ω)
  (Formula.existsMem A (Formula.existsMem A.weaken
    (.conj (rd_triple0_m u.weaken.weaken A.weaken.weaken R.weaken.weaken (.bound 1))
      (.conj (rd_triple0_m v.weaken.weaken A.weaken.weaken R.weaken.weaken .newest)
        (rd_entry0_m (.bound 1) .newest R.weaken.weaken)))))
derive_free_closed sb_edge_m

theorem sb_edge_delta_l {n} (ω A R u v : Term n) : (sb_edge_m ω A R u v).IsDelta0 :=
  .conj (omega0_delta_l _) (.existsMem _ (.existsMem _ (.conj (rd_triple0_delta_l ..)
    (.conj (rd_triple0_delta_l ..) (rd_entry0_delta_l ..)))))

theorem sb_edge_sat_l (hE : Extensional M) {n} (ρ : Env M n) (ω A R u v : Term n) :
    Formula.satisfies ρ (sb_edge_m ω A R u v) ↔ Omega0_d (ω.eval ρ) ∧
      Sb_edge_d (A.eval ρ) (R.eval ρ) (u.eval ρ) (v.eval ρ) := by
  simp only [sb_edge_m, Sb_edge_d, Formula.satisfies_conj_iff, omega0_sat_l hE,
    Formula.satisfies_existsMem_iff, rd_triple0_sat_l hE, rd_entry0_sat_l hE, Definitional.Term.eval_weaken]; rfl

def Sb_bad_d (ω X u v : M.Domain) : Prop := ∃ A R, M.mem A X ∧ M.mem R X ∧
  Sb_edge_d A R u v ∧ ¬ ∃ f, M.mem f X ∧ Sb_chain_d ω A R f

def sb_bad_m : Formula 1 2 := .existsE (.existsE (.existsE
  (.conj (sb_edge_m (.bound 2) (.bound 1) .newest (.bound 4) (.bound 3))
    (.neg (.existsE (sb_chain_m (.bound 3) (.bound 2) (.bound 1) .newest))))))

theorem sb_bad_closed_l : sb_bad_m.FreeClosed := by
  simp -implicitDefEqProofs [sb_bad_m, Definitional.Formula.FreeClosed]

theorem sb_bad_sat_l (hZF : M.Models ZF) {ω c X R : M.Domain} (hω : M.IsOmega ω)
    (hX : M.TransitiveSet X) (hωX : M.mem ω X) (hm : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R)
    (ρ : Env (smdl_structure_l (kp_pair_l (ZF.modelsKP hZF)) (R := R) hm.1.2.1) 2) :
    Formula.satisfies ρ sb_bad_m ↔ Sb_bad_d ω X (ρ.bound 1).val (ρ.bound 0).val := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  let N := smdl_structure_l I (R := R) hm.1.2.1
  have edge (η : Env N 5) := (smem_delta_image_l I hm hX
    (sb_edge_delta_l (.bound 2) (.bound 1) .newest (.bound 4) (.bound 3)) η).trans (sb_edge_sat_l hZF.1 ..)
  have chain (η : Env N 6) := (smem_delta_image_l I hm hX
    (sb_chain_delta_l (.bound 3) (.bound 2) (.bound 1) .newest) η).trans (sb_chain_sat_l hZF.1 ..)
  simp only [sb_bad_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_neg_iff, edge, chain]
  constructor
  · rintro ⟨Ω, A, S, ⟨ho, he⟩, no⟩
    have eq := (omega0_iff_l (ZF.models_kpi_l hZF) hω).mp ho
    exact ⟨A.val, S.val, A.property, S.property, he, fun ⟨f, hf, h⟩ => no ⟨⟨f, hf⟩, eq.symm ▸ h⟩⟩
  · rintro ⟨A, S, hA, hS, he, no⟩
    exact ⟨⟨ω, hωX⟩, ⟨A, hA⟩, ⟨S, hS⟩, ⟨(omega0_iff_l (ZF.models_kpi_l hZF) hω).mpr rfl, he⟩,
      fun ⟨f, hf⟩ => no ⟨f.val, f.property, hf⟩⟩

end YesMetaZFC.SetTheory.Internal
