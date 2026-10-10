import YesMetaZFC.SetTheory.LargeCardinal.ExtenderStrengthPull
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderReadSource
import YesMetaZFC.Model.SetTheory.Internal.SourceInaccessible

/-! # 所属短扩展器、不可达性和有限幂一致性的回拉

所属模型中的原公式沿实际限制反射；子集一致性只在有一侧隶属时取该子集
的初等像，因而无需假定壳包含所有背景子集。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem It_local_d.pull_l {ω X R Y S c d σ κ κ' L L' F F' : M.Domain}
    (hω : M.IsOmega ω) (mx : Smem_d I c X R) (my : Smem_d I d Y S) (hs : Smap_d I ω c d X Y σ)
    (hw : Rd_entry_d ω ω σ) (hk : Rd_entry_d κ κ' σ) (hl : Rd_entry_d L L' σ) (hf : Rd_entry_d F F' σ)
    (loc : It_local_d ω Y κ' L' F') : It_local_d ω X κ L F := by
  have owned {a b} (h : Rd_entry_d a b σ) := hs.1.1.input_mem_of_pairMember h
  obtain ⟨ωY, κY, LY, FY, loc⟩ := loc
  let ρ : Env (rt_model_l X ⟨⟨ω, owned hw⟩⟩) 4 :=
    ⟨Fin.cases ⟨F, owned hf⟩ (Fin.cases ⟨L, owned hl⟩ (Fin.cases ⟨κ, owned hk⟩ (fun _ => ⟨ω, owned hw⟩))), fun _ => ⟨ω, owned hw⟩⟩
  let η : Env (rt_model_l Y ⟨⟨ω, ωY⟩⟩) 4 :=
    ⟨Fin.cases ⟨F', FY⟩ (Fin.cases ⟨L', LY⟩ (Fin.cases ⟨κ', κY⟩ (fun _ => ⟨ω, ωY⟩))), fun _ => ⟨ω, ωY⟩⟩
  let φ : Formula 1 4 := ex_short_m (.bound 3) (.bound 2) (.bound 1) (.bound 0)
  have tr := smap_source_l I hZF hω mx.1 my.1 hs φ (by simp -implicitDefEqProofs [φ])
    ⟨ρ.bound, ρ.free⟩ ⟨η.bound, η.free⟩ (Fin.cases hf (Fin.cases hl (Fin.cases hk (fun _ => hw))))
  exact ⟨owned hw, owned hk, owned hl, owned hf,
    (smem_formula_l I mx _ φ ρ).mpr (tr.mpr ((smem_formula_l I my _ φ η).mp loc))⟩

theorem _root_.YesMetaZFC.SetTheory.Internal.Sc_inaccessible_d.pull_l
    {ω X R Y S c d σ κ κ' : M.Domain} (hω : M.IsOmega ω)
    (mx : Smem_d I c X R) (my : Smem_d I d Y S) (hs : Smap_d I ω c d X Y σ)
    (hw : Rd_entry_d ω ω σ) (hk : Rd_entry_d κ κ' σ)
    (big : Sc_inaccessible_d ω Y κ') : Sc_inaccessible_d ω X κ := by
  have hωX := hs.1.1.input_mem_of_pairMember hw
  have hκX := hs.1.1.input_mem_of_pairMember hk
  obtain ⟨hωY, hκY, h⟩ := big
  let ρ : Env (rt_model_l X ⟨⟨ω, hωX⟩⟩) 2 := ⟨Fin.cases ⟨κ, hκX⟩ (fun _ => ⟨ω, hωX⟩), fun _ => ⟨ω, hωX⟩⟩
  let η : Env (rt_model_l Y ⟨⟨ω, hωY⟩⟩) 2 := ⟨Fin.cases ⟨κ', hκY⟩ (fun _ => ⟨ω, hωY⟩), fun _ => ⟨ω, hωY⟩⟩
  let φ : Formula 1 2 := sc_inaccessible_m (.bound 1) .newest
  have tr := smap_source_l I hZF hω mx.1 my.1 hs φ (by simp -implicitDefEqProofs [φ])
    ⟨ρ.bound, ρ.free⟩ ⟨η.bound, η.free⟩ (Fin.cases hk (fun _ => hw))
  exact ⟨hωX, hκX, (smem_formula_l I mx _ φ ρ).mpr (tr.mpr ((smem_formula_l I my _ φ η).mp h))⟩

theorem Ea_agree_d.pull_l {ω B R b U S u π κ κ' X X' Y Y' : M.Domain}
    (hω : M.IsOmega ω) (ambient : Fs_read_d ω B) (target : Fs_read_d ω U)
    (mb : Smem_d I b B R) (mu : Smem_d I u U S) (hj : Smap_d I ω b u B U π)
    (hk : Rd_entry_d κ κ' π) (hx : Rd_entry_d X X' π) (hy : Rd_entry_d Y Y' π)
    (big : Ea_agree_d ω κ' X' Y') : Ea_agree_d ω κ X Y := by
  have bt := ambient.transitive
  have ut := target.transitive
  intro n D A hn hd sub
  obtain ⟨D₀, hD, space⟩ := ambient.spaces κ n (hj.1.1.input_mem_of_pairMember hk) hn
  have eq := hZF.1.eq_of_same_members D₀ D (fun f => (space f).trans (hd f).symm)
  subst D₀
  obtain ⟨D', hD', hDD⟩ := hj.1.1.2.2 D hD
  have nat := hj.natural_l hZF hω bt ut mb mu ambient.omega_mem n hn
  have tr := hj.forall_delta_l hZF hω bt ut mb mu
    (.iff (.mem (.newest : Term 4) (.bound 1)) (fn0_m (.bound 3) (.bound 2) .newest))
    (by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]) (.iff (.mem ..) (fn0_delta_l ..))
    ⟨Fin.cases D (Fin.cases κ (fun _ => n)), fun _ => n⟩
    ⟨Fin.cases D' (Fin.cases κ' (fun _ => n)), fun _ => n⟩ (Fin.cases hDD (Fin.cases hk (fun _ => nat)))
  simp only [Formula.satisfies_iff_iff, Formula.satisfies_mem_iff, fn0_sat_l hZF.1] at tr
  have values := tr.mp (fun f _ => hd f)
  have hd' : Ep_space_d κ' n D' := fun f => ⟨fun hf => (values f (ut D' hD' f hf)).mp hf,
    fun hf => (values f (target.functions n κ' f hn (ut κ' (hj.1.1.output_mem_of_pairMember hk)) hf)).mpr hf⟩
  have read (owned : M.mem A B) : M.mem A X ↔ M.mem A Y := by
    obtain ⟨A', _, hAA⟩ := hj.1.1.2.2 A owned
    have agree := big n D' A' hn hd' ((hj.subset_l hZF hω bt ut mb mu hAA hDD).mp sub)
    exact (hj.member_l I hZF hω mb mu hAA hx).trans (agree.trans (hj.member_l I hZF hω mb mu hAA hy).symm)
  exact ⟨fun h => (read (bt X (hj.1.1.input_mem_of_pairMember hx) A h)).mp h,
    fun h => (read (bt Y (hj.1.1.input_mem_of_pairMember hy) A h)).mpr h⟩

end YesMetaZFC.SetTheory.LargeCardinal
