import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.SourceTruth
import YesMetaZFC.Model.SetTheory.Internal.PointwiseWitness
import YesMetaZFC.SetTheory.Filter.Source

/-! # 源内部函数族的完整内部 Łoś 定理

在实际原公式 rs_los_m 上作内部行归纳。或非步使用源内真值逆像，存在步
调用已构造的源内统一代表；商始终只使用源中实际拥有的函数图。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem rs_los_l {ω c X R D P U o G p C T E K F n b r}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hm : Smem_d I c X R)
    (theory : Sc_theory_d I ω X R) (uniform : Sc_uniform_d I ω X R D) (hD : M.mem D X) (hP : FilterZF.Source_d X D P)
    (hU : FilterZF.Rel_ultra_d D P U) (hG : ∀ g, M.mem g G ↔ M.mem g X ∧ Fn0_d D X g)
    (hM : Rp_model_d I D X U R o G p C T) (hE : M.IsFunctionSpace I E ω X)
    (hK : M.IsFunctionSpace I K ω C) (hF : Sfm_d I ω n F)
    (hb : M.mem b ω) (hB : Sbound_d I F b) (hr : M.mem r n) : Rs_los_d I b D X R E F n U p C T K r := by
  obtain ⟨V, hV⟩ := seval_exists_l I hZF X R E F hF.2.1.1
  obtain ⟨J, hJ⟩ := seval_exists_l I hZF C T K F hF.2.1.1
  let ρ : Env M 12 := ⟨Fin.cases K (Fin.cases T (Fin.cases C (Fin.cases p (Fin.cases U (Fin.cases n
    (Fin.cases F (Fin.cases E (Fin.cases R (Fin.cases X (Fin.cases D (fun _ => b))))))))))), fun _ => b⟩
  let φ : UnarySchema 12 := {
    body := rs_los_m (𝒞 := kpair_convention_l) (.bound 12) (.bound 11) (.bound 10) (.bound 9) (.bound 8)
      (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have sat s : φ.denote ρ s ↔ Rs_los_d I b D X R E F n U p C T K s := rs_los_sat_l I hZF.1 ..
  suffices h : φ.denote ρ r from (sat r).mp h
  apply sfm_induction_l I hZF hF φ ρ ?_ hr
  intro r hr ih
  apply (sat r).mpr
  intro a e ha he hv
  have repr := hv.repr_l I ((hE a).mp ha).1
  have bω := hω.transitive hZF b hb
  have trace s (hs : M.mem s n) : ∃ A, M.mem A P ∧
      ∀ v, M.mem v A ↔ M.mem v D ∧ Pe_sat_d I b D X R E F n s a v := by
    obtain ⟨A, hAX, hA⟩ := sc_pe_trace_l hZF hω hX hm theory hD hE hF hs hb hB ha repr
    exact ⟨A, (hP A).mpr ⟨hAX, fun v hv => ((hA v).mp hv).1⟩, hA⟩
  obtain ⟨z, hz⟩ := (hF.2.1.2.2 r).mp hr
  rcases hF.2.2 r z hz with ⟨i, j, hs, _, _⟩ | ⟨i, j, hs, _, _⟩ |
    ⟨i, j, hs, hi, hj⟩ | ⟨i, j, hs, hi, hj⟩
  · obtain ⟨hib, hjb⟩ := hB.operands_l I hz hs
    obtain ⟨g, B, hig, hg, hgp, hie⟩ := hv i hib
    obtain ⟨f, A, hjf, hf, hfp, hje⟩ := hv j hjb
    have atom : Pe_holds_d I b D X R E F n r U a ↔ Rp_rel_d I X U R g f := by
      apply exists_congr
      intro W
      apply and_congr_right
      intro hW
      apply forall_congr'
      intro v
      apply imp_congr_right
      intro hvW
      have hvD := hU.base.bounds W hW v hvW
      have read x y (hx : Rd_entry_d v x g) (hy : Rd_entry_d v y f) :=
        pe_sat_atom_l I hZF hX hE hF hV hB bω ha repr hvD hm.1.2.1 hz false hs hig hjf hx hy
      refine ⟨fun ht => ?_, fun ⟨x, _, y, _, hx, hy, hxy⟩ => (read x y hx hy).mpr hxy⟩
      obtain ⟨x, hx, hvx⟩ := (hg.function_l hX).2.1 v hvD
      obtain ⟨y, hy, hvy⟩ := (hf.function_l hX).2.1 v hvD
      exact ⟨x, hx, y, hy, hvx, hvy, (read x y hvx hvy).mp ht⟩
    exact atom.trans ((hM.relation g f B A hgp hfp).symm.trans (ssat_rel_l I hZF hF hJ hz hs hK he hie hje).symm)
  · obtain ⟨hib, hjb⟩ := hB.operands_l I hz hs
    obtain ⟨g, B, hig, hg, hgp, hie⟩ := hv i hib
    obtain ⟨f, A, hjf, hf, hfp, hje⟩ := hv j hjb
    have atom : Pe_holds_d I b D X R E F n r U a ↔ Rp_eq_d X U g f := by
      apply exists_congr
      intro W
      apply and_congr_right
      intro hW
      apply forall_congr'
      intro v
      apply imp_congr_right
      intro hvW
      have hvD := hU.base.bounds W hW v hvW
      have read x y (hx : Rd_entry_d v x g) (hy : Rd_entry_d v y f) :=
        pe_sat_atom_l I hZF hX hE hF hV hB bω ha repr hvD hm.1.2.1 hz true hs hig hjf hx hy
      refine ⟨fun ht => ?_, fun ⟨x, _, hx, hy⟩ => (read x x hx hy).mpr rfl⟩
      obtain ⟨x, hx, hvx⟩ := (hg.function_l hX).2.1 v hvD
      obtain ⟨y, _, hvy⟩ := (hf.function_l hX).2.1 v hvD
      exact ⟨x, hx, hvx, ((read x y hvx hvy).mp ht).symm ▸ hvy⟩
    exact atom.trans ((rp_kernel_l I hZF.1 hU.base hM.map hgp hfp).symm.trans
      (ssat_eq_l I hZF hF hJ hz hs hK he hie hje).symm)
  · have hin := hF.2.1.1.transitive r hr i hi
    have hjn := hF.2.1.1.transitive r hr j hj
    obtain ⟨A, hA, hsA⟩ := trace i hin
    obtain ⟨B, hB', hb'⟩ := trace j hjn
    obtain ⟨W, hW, hw⟩ := trace r hr
    exact (pe_holds_nor_l I hU hA hB' hW hsA hb' hw
      (fun v hvD => pe_sat_nor_l I hZF hX hE hF hV hB bω ha repr hvD hm.1.2.1 hz hs hin hjn)).trans
      ((not_congr (or_congr ((sat i).mp (ih i hi) a e ha he hv)
        ((sat j).mp (ih j hj) a e ha he hv))).trans (ssat_nor_l I hZF hF hJ hz hs he).symm)
  · have hjn := hF.2.1.1.transitive r hr j hj
    rw [ssat_exists_l I hZF hF hJ hz hs he]
    constructor
    · rintro ⟨A, hA, ht⟩
      obtain ⟨g, a', hg, ha', hs'⟩ := sc_pe_witness_l hZF hω hX hm theory uniform hD hE hF hV hz hs hjn hb hB
        ha ((hP A).mp (hU.admissible A hA)).1 (hU.base.bounds A hA) ht
      obtain ⟨B, hBC, hgp⟩ := hM.map.projection.2.2 g ((hG g).mpr ⟨hg.1, hg.function_l hX⟩)
      obtain ⟨e', he', heK⟩ := senv_update_exists_l I hZF ((hK e).mp he) hi hBC
      exact ⟨B, e', hBC, he', ((sat j).mp (ih j hj) a' e'
        ((hE a').mpr (ha'.function_l I ((hE a).mp ha) hi hg.1)) ((hK e').mpr heK)
        (hv.update_l I hg hgp ha' he')).mp ⟨A, hA, hs'⟩⟩
    · rintro ⟨B, e', hBC, he', ht⟩
      obtain ⟨g, hgp⟩ := (hM.map.range B).mp hBC
      obtain ⟨hgX, hgD⟩ := (hG g).mp (hM.map.projection.input_mem_of_pairMember hgp)
      have hg := sc_function_domain_l theory.algebra hgX hgD
      obtain ⟨a', ha', haE⟩ := senv_update_exists_l I hZF ((hE a).mp ha) hi hgX
      obtain ⟨A, hA, hA'⟩ := ((sat j).mp (ih j hj) a' e' ((hE a').mpr haE)
        ((hK e').mpr (he'.function_l I ((hK e).mp he) hi hBC)) (hv.update_l I hg hgp ha' he')).mpr ht
      exact ⟨A, hA, fun v hvA => pe_sat_ex_intro_l I hZF hX hE hF hV hB bω ha repr
        (hU.base.bounds A hA v hvA) hm.1.2.1 hz hs hi hjn hg ha' (hA' v hvA)⟩

end YesMetaZFC.SetTheory.Internal
