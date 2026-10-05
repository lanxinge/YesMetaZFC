import YesMetaZFC.Model.SetTheory.Internal.EmbeddingFinite
import YesMetaZFC.SetTheory.KP.Ordinal
import YesMetaZFC.SetTheory.MembershipInduction

/-! # 初等映射在序数上不下降

序数性的保持用 Δ₀ 刻画；不下降性对原图公式作内部成员归纳，
不要求背景模型外部良基，也不以外部递归替代模型中的证明。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ordinal_down_l (hKP : M.Models KP) {a b c : M.Domain} (ha : M.IsOrdinal a) (hc : M.IsOrdinal c)
    (hab : M.MemberSubset a b) (hbc : M.mem b c) : M.mem a c := by
  rcases ha.trichotomy hKP.1 (hc.mem hbc) (KP.difference_exists_d hKP)
    (KP.intersection_exists_d hKP a b) with eq | lt | gt
  · exact (hKP.1.eq_of_same_members a b eq).symm ▸ hbc
  · exact hc.transitive b hbc a lt
  · exact (KP.mem_irrefl_d hKP b (hab b gt)).elim

theorem Smap_d.ordinal_l {ω c d X R Y S j a b : M.Domain} (hω : M.IsOmega ω)
    (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y) (hm : Smem_d I c X R) (hn : Smem_d I d Y S)
    (hj : Smap_d I ω c d X Y j) (hab : Rd_entry_d a b j) (ha : M.IsOrdinal a) : M.IsOrdinal b := by
  have tr := smap_delta_l I hZF hω hX hY hm hn hj (n := 1) (KP.ord0_m (.bound 0))
    (by simp -implicitDefEqProofs) (KP.ord0_delta_l ..)
    ⟨fun _ => a, fun _ => a⟩ ⟨fun _ => b, fun _ => b⟩ (fun _ => hab)
  exact (KP.ord0_sat_l (ZF.modelsKP hZF) ..).mp (tr.mp ((KP.ord0_sat_l (ZF.modelsKP hZF) ..).mpr ha))

theorem Smap_d.ordinal_le_l {ω c d X R Y S j a b : M.Domain} (hω : M.IsOmega ω)
    (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y) (hm : Smem_d I c X R) (hn : Smem_d I d Y S)
    (hj : Smap_d I ω c d X Y j) (hab : Rd_entry_d a b j) (ha : M.IsOrdinal a) : M.MemberSubset a b := by
  let ρ : Env M 1 := ⟨fun _ => j, fun _ => j⟩
  let φ : UnarySchema 1 := { body := .imp (KP.ord0_m .newest) (.forallE
    (.imp (rd_entry0_m (.bound 1) .newest (.bound 2)) (Formula.subset (.bound 1) .newest))) }
  have sat α : φ.denote ρ α ↔ M.IsOrdinal α → ∀ β, Rd_entry_d α β j → M.MemberSubset α β := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_imp_iff, KP.ord0_sat_l (ZF.modelsKP hZF),
      Formula.satisfies_forall_iff, rd_entry0_sat_l hZF.1, Formula.satisfies_subset_iff]; rfl
  apply (sat a).mp (ZF.mem_ind_l M hZF I φ ρ ?_ a) ha b hab
  intro α ih
  apply (sat α).mpr
  intro hα β hαβ γ hγα
  have hαX := hj.1.1.input_mem_of_pairMember hαβ
  have hγX := hX α hαX γ hγα
  obtain ⟨δ, _, hγδ⟩ := hj.1.1.2.2 γ hγX
  have hδβ := ((hn.2 δ β).mp ((hj.relation_l I hZF hω hm.1 hn.1 hγδ hαβ).mp
    ((hm.2 γ α).mpr ⟨hγX, hαX, hγα⟩))).2.2
  exact ordinal_down_l (ZF.modelsKP hZF) (hα.mem hγα) (hj.ordinal_l hZF hω hX hY hm hn hαβ hα)
    ((sat γ).mp (ih γ hγα) (hα.mem hγα) δ hγδ) hδβ

end YesMetaZFC.SetTheory.Internal
