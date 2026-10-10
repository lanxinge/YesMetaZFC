import YesMetaZFC.SetTheory.LargeCardinal.ExtenderTransport
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderComponents
import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.Copy
import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.Restriction

/-! # 双映射复制的实际分量

支撑由所属模型的 σ 搬运，代表由施加源的 π 搬运。两图在有限 κ 幂的
源子集上相同，配合 σ(F)=F′，实际推出测度成员对应，再构造完整初等复制。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal FilterZF
universe u
variable {M : Structure.{u}}

def Ea_maps_d (ω κ X π σ : M.Domain) : Prop := ∀ n D A A', M.mem n ω → Ep_space_d κ n D →
  M.mem A X → M.MemberSubset A D → Rd_entry_d A A' π → Rd_entry_d A A' σ

def Ec_class_d (π B C : M.Domain) : Prop := ∃ f g, M.mem f B ∧ M.mem g C ∧ Rd_entry_d f g π

def ec_class_m {d} (π B C : Term d) : Formula 1 d := Formula.existsMem B (Formula.existsMem C.weaken
  (rd_entry_m (.bound 1) .newest π.weaken.weaken))
derive_free_closed ec_class_m

theorem ec_class_sat_l (hE : Extensional M) {d} (ρ : Env M d) (π B C : Term d) :
    Formula.satisfies ρ (ec_class_m π B C) ↔ Ec_class_d (π.eval ρ) (B.eval ρ) (C.eval ρ) := by
  simp only [ec_class_m, Ec_class_d, Formula.satisfies_existsMem_iff, rd_entry_sat_l hE, Definitional.Term.eval_weaken]
  exact ⟨fun ⟨f, hf, g, hg, h⟩ => ⟨f, g, hf, hg, h⟩, fun ⟨f, g, hf, hg, h⟩ => ⟨f, hf, g, hg, h⟩⟩

theorem ec_component_l (hZFC : M.Models ZFC)
    {ω κ κ' K K' L L' X R Y S N R₀ N' R₁ c d b b' π σ F F' a a' o o' : M.Domain}
    (source : Ep_source_d (ZFC.models_zf_l hZFC) ω κ K X R)
    (target : Ep_source_d (ZFC.models_zf_l hZFC) ω κ' K' Y S)
    (hm : Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) c X R)
    (hn : Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) d Y S)
    (hπ : Smap_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω c d X Y π)
    (hκ : Rd_entry_d κ κ' π) (owner : M.TransitiveSet N) (owner' : M.TransitiveSet N')
    (h₀ : Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) b N R₀)
    (h₁ : Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) b' N' R₁)
    (hσ : Smap_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω b b' N N' σ)
    (hωN : M.mem ω N) (hL : Rd_entry_d L L' σ) (hF : Rd_entry_d F F' σ)
    (family : Em_source_d ω κ L X F) (family' : Em_source_d ω κ' L' Y F') (agree : Ea_maps_d ω κ X π σ)
    (haa : Rd_entry_d a a' σ)
    (hM : Ep_component_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ L X R F a o)
    (hM' : Ep_component_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ' L' Y S F' a' o') :
    let I := kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))
    ∃ C T C' T' e, Smdl_d I o C T ∧ Smdl_d I o' C' T' ∧ Smap_d I ω o o' C C' e ∧
      (∀ B D, Rd_entry_d B D e ↔ M.mem B C ∧ M.mem D C' ∧ Ec_class_d π B D) ∧
      ∀ B D f g, M.mem B C → M.mem D C' → Ec_class_d π B D → M.mem f B → Rd_entry_d f g π → M.mem g D := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨n, D, U, G, p, C, T, hnω, ha, space, haU, hG, model⟩ := hM
  obtain ⟨n', E, V, H, p', C', T', _, ha', space', haV, hH, model'⟩ := hM'
  have hna := (hσ.function_l hZF source.omega owner owner' h₀ h₁
    (hσ.natural_l hZF source.omega owner owner' h₀ h₁ hωN n hnω) hL haa).mp ha
  have en := ha'.domain_eq_l hZF.1 hna
  subst n'
  obtain ⟨D', _, hDD⟩ := hπ.1.1.2.2 D (source.space_mem_l hZF hnω space)
  have image := ep_space_map_l hZF source target hm hn hπ hκ hnω space hDD
  have eD := hZF.1.eq_of_same_members D' E (fun s => (image s).trans (space' s).symm)
  subst D'
  have hu := family.at_l hZF.1 haU ha space
  have hv := family'.at_l hZF.1 haV ha' space'
  obtain ⟨P, U', hp, hu', us, model₀⟩ := rs_restrict_model_l hZF source.omega source.transitive hm source.theory
    (source.space_mem_l hZF hnω space) hu hG model
  obtain ⟨Q, V', hq, hv', vs, model₁⟩ := rs_restrict_model_l hZF target.omega target.transitive hn target.theory
    (target.space_mem_l hZF hnω space') hv hH model'
  have measures A A' (hA : M.mem A P) (hAA : Rd_entry_d A A' π) : M.mem A U' ↔ M.mem A' V' := by
    have hAQ := (hq A').mpr ⟨hπ.1.1.output_mem_of_pairMember hAA,
      (hπ.subset_l hZF source.omega source.transitive target.transitive hm hn hAA hDD).mp ((hp A).mp hA).2⟩
    have eq := ec_measure_image_l hZF source.omega owner owner' h₀ h₁ hσ hF haa
      (agree n D A A' hnω space ((hp A).mp hA).1 ((hp A).mp hA).2 hAA) haU haV family'.function
    exact ((us A).trans ⟨And.right, fun h => ⟨hA, h⟩⟩).trans
      (eq.trans ((vs A').trans ⟨And.right, fun h => ⟨hAQ, h⟩⟩).symm)
  obtain ⟨Qf, e, hf, fs, he, lift⟩ := rs_copy_embedding_l hZFC source.omega source.transitive target.transitive hm hn hπ
    source.theory target.theory hDD hp hq hu' hv' measures hG hH model₀ model₁
  have spec : ∀ B D, Rd_entry_d B D e ↔ M.mem B C ∧ M.mem D C' ∧ Ec_class_d π B D := by
    intro B D
    constructor
    · intro hBD
      have hBC := he.1.1.input_mem_of_pairMember hBD
      obtain ⟨f, hfp⟩ := (model.map.range B).mp hBC
      obtain ⟨g, hg, hfg⟩ := hf.2.2 f (model.map.projection.input_mem_of_pairMember hfp)
      obtain ⟨D', _, hgp⟩ := model'.map.projection.2.2 g hg
      have eq := he.1.1.1.2 B D' D (lift f g B D' hfg hfp hgp) hBD
      exact ⟨hBC, he.1.1.output_mem_of_pairMember hBD, f, g, model.map.representative_l I hu.base hfp,
        eq ▸ model'.map.representative_l I hv.base hgp, ((fs f g).mp hfg).2⟩
    · rintro ⟨hB, hD, f, g, hfB, hgD, hfg⟩
      have hfp := model.map.member_l I hZF.1 hu.base hB hfB
      have hgp := model'.map.member_l I hZF.1 hv.base hD hgD
      exact lift f g B D ((fs f g).mpr ⟨model.map.projection.input_mem_of_pairMember hfp, hfg⟩) hfp hgp
  refine ⟨C, T, C', T', e, model.code, model'.code, he, spec, fun B D f g hB hD hc hfB hfg => ?_⟩
  have hfp := model.map.member_l I hZF.1 hu.base hB hfB
  have hfg' := (fs f g).mpr ⟨model.map.projection.input_mem_of_pairMember hfp, hfg⟩
  obtain ⟨D', _, hgp⟩ := model'.map.projection.2.2 g (hf.output_mem_of_pairMember hfg')
  have eq := he.1.1.1.2 B D' D (lift f g B D' hfg' hfp hgp) ((spec B D).mpr ⟨hB, hD, hc⟩)
  exact eq ▸ model'.map.representative_l I hv.base hgp

end YesMetaZFC.SetTheory.LargeCardinal
