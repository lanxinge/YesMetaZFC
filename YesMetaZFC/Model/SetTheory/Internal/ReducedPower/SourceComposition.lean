import YesMetaZFC.Model.SetTheory.Internal.UniformizationSource
import YesMetaZFC.SetTheory.InnerModel.Recursion.Composition

/-! # 源内部代表沿实际坐标函数的拉回

有界的复合关系在源内统一化，得到真正属于源的复合图。再以唯一值收集
同时构造整个代表族上的拉回图，不为不同分量选择不同实现。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem sc_compose_l {ω c X R A B t f} (hω : M.IsOmega ω)
    (hX : M.TransitiveSet X) (hm : Smem_d I c X R)
    (theory : Sc_theory_d I ω X R)
    (hA : M.mem A X) (hB : M.mem B X) (htX : M.mem t X) (hfX : M.mem f X)
    (ht : Fn0_d A B t) (hf : Fn0_d B X f) : ∃ g, Sfun_d X A g ∧ Cp0_d A B X t f g := by
  let ρ : Env M 3 := ⟨Fin.cases f (Fin.cases t (fun _ => B)), fun _ => B⟩
  let φ : BinarySchema 3 := {
    body := Formula.existsMem (.bound 4)
      (.conj (rd_entry0_m (.bound 2) .newest (.bound 4)) (rd_entry0_m .newest (.bound 1) (.bound 3))) }
  have sat v x : φ.denote ρ v x ↔ ∃ w, M.mem w B ∧ Rd_entry_d v w t ∧ Rd_entry_d w x f := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff, rd_entry0_sat_l hZF.1]
    rfl
  obtain ⟨C, hC, bound⟩ := theory.algebra.envelope_l hfX
  obtain ⟨g, hg, hgf, hs⟩ := sc_uniform_source_l hZF hω hX hm theory φ
    (.existsMem _ (.conj (rd_entry0_delta_l ..) (rd_entry0_delta_l ..))) ρ (Fin.cases hfX (Fin.cases htX (fun _ => hB))) hA hC
    (fun v hv => by
      obtain ⟨w, hw, hvw⟩ := ht.2.1 v hv
      obtain ⟨x, _, hwx⟩ := hf.2.1 w hw
      exact ⟨x, (bound w x hwx).2, (sat v x).mpr ⟨w, hw, hvw, hwx⟩⟩)
  refine ⟨g, ⟨hg, C, hC, hgf⟩, hgf.mono_target_l (hX C hC), fun v hv => ?_⟩
  obtain ⟨x, hx, hvx⟩ := hgf.2.1 v hv
  obtain ⟨w, hw, hvw, hwx⟩ := (sat v x).mp (hs v x hvx)
  exact ⟨w, hw, x, hX C hC x hx, hvw, hwx, hvx⟩

theorem rs_pullback_family_l {ω c X R A B t F G} (hω : M.IsOmega ω)
    (hX : M.TransitiveSet X) (hm : Smem_d I c X R)
    (theory : Sc_theory_d I ω X R)
    (hA : M.mem A X) (hB : M.mem B X) (htX : M.mem t X) (ht : Fn0_d A B t)
    (hF : ∀ f, M.mem f F ↔ M.mem f X ∧ Fn0_d B X f)
    (hG : ∀ g, M.mem g G ↔ M.mem g X ∧ Fn0_d A X g) : ∃ K, M.IsSetFunctionFromTo I K F G ∧
      ∀ f g, M.PairMember I f g K ↔ M.mem f F ∧ M.mem g G ∧ Cp0_d A B X t f g := by
  let ρ : Env M 5 := ⟨Fin.cases G (Fin.cases t (Fin.cases X (Fin.cases B (fun _ => A)))), fun _ => A⟩
  let φ : BinarySchema 5 := {
    body := .conj (.mem .newest (.bound 2)) (cp0_m (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 1) .newest) }
  have sat f g : φ.denote ρ f g ↔ M.mem g G ∧ Cp0_d A B X t f g := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, cp0_sat_l hZF.1]
    rfl
  obtain ⟨K, hK, spec⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := F) (target := G)
    (fun f hf => by
      obtain ⟨g, hg, hc⟩ := sc_compose_l hZF hω hX hm theory hA hB htX ((hF f).mp hf).1 ht ((hF f).mp hf).2
      exact ⟨g, (sat f g).mpr ⟨(hG g).mpr ⟨hg.1, hc.1⟩, hc⟩⟩)
    (fun f hf g k hg hk => cp0_unique_l hZF.1 ht ((hF f).mp hf).2 ((sat f g).mp hg).2 ((sat f k).mp hk).2)
    (fun f g _ hg => ((sat f g).mp hg).1)
  exact ⟨K, hK, fun f g => (spec f g).trans (and_congr_right fun _ => sat f g)⟩

end YesMetaZFC.SetTheory.Internal
