import YesMetaZFC.SetTheory.LargeCardinal.ExtenderRepresentative
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderElementary
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderConstant
import YesMetaZFC.Model.SetTheory.Internal.EmbeddingFinite
import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.DeltaImage

/-! # 关系实现中的实际代表与完整公式

固定分量先进入原始关系极限。完整公式直接在关系实现中解释；只有把
有界公式读成背景集合性质时才要求目标传递。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Ep_value_d (q e a f x : M.Domain) : Prop := ∃ E, Ep_repr_d q a f E ∧ Rd_entry_d E x e

def ep_value_m {d} (q e a f x : Term d) : Formula 1 d := .existsE
  (.conj (ep_repr_m q.weaken a.weaken f.weaken .newest) (rd_entry_m .newest x.weaken e.weaken))
derive_free_closed ep_value_m

theorem ep_value_sat_l (hE : Extensional M) {d} (ρ : Env M d) (q e a f x : Term d) :
    Formula.satisfies ρ (ep_value_m q e a f x) ↔
      Ep_value_d (q.eval ρ) (e.eval ρ) (a.eval ρ) (f.eval ρ) (x.eval ρ) := by
  simp only [ep_value_m, Ep_value_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    ep_repr_sat_l hE, rd_entry_sat_l hE, Definitional.Term.eval_weaken]; rfl

/-- 同一实际代表的值唯一；只用原商的等号核和实现图的函数性。 -/
theorem Ep_value_d.unique_l (hZF : M.Models ZF)
    {ω κ L X R F J O Z A p T V q C W N e a f x y : M.Domain}
    (family : Em_source_d ω κ L X F)
    (system : Ep_system_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L X R F J O Z A p T V) (limit : Di_limit_d A p T V q C W)
    (he : Fn0_d C N e) (hx : Ep_value_d q e a f x) (hy : Ep_value_d q e a f y) : x = y := by
  obtain ⟨E, fv, hEx⟩ := hx
  obtain ⟨H, fw, hHy⟩ := hy
  obtain ⟨_, n, hn, ha, _⟩ := fv.source_l hZF family system limit
  obtain ⟨U, haU⟩ := family.total n a hn ha
  have eq := (ep_repr_atoms_l hZF family system limit haU fv fw).1.mpr
    ((ep_repr_atoms_l hZF family system limit haU fv fv).1.mp rfl)
  exact (fn0_function_l (ZF.modelsKP hZF) he).1.2 H x y (eq ▸ hEx) hHy

theorem ep_formula_value_l (hZFC : M.Models ZFC) {ω κ K L X R F J O Z A p T V q c C W d N S e n D a U : M.Domain}
    (source : Ep_source_d (ZFC.models_zf_l hZFC) ω κ K X R) (family : Em_source_d ω κ L X F)
    (coherent : Ec_source_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ L X F)
    (h : Ep_system_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ L X R F J O Z A p T V) (limit : Di_limit_d A p T V q C W)
    (model : Smdl_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) c C W)
    (target : Smdl_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) d N S)
    (he : Smap_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω c d C N e)
    (haJ : M.mem a J) (ha : Fn0_d n L a) (hD : Ep_space_d κ n D) (haU : Rd_entry_d a U F)
    {k} (φ : Formula 1 k) (hφ : φ.FreeClosed) (f : Fin k → M.Domain)
    (ρ : Env (smdl_structure_l (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) (R := S) target.2.1) k)
    (values : ∀ i, Ep_value_d q e a (f i) (ρ.bound i).val) :
    Formula.satisfies ρ φ ↔ ∃ B, M.mem B X ∧ M.mem B U ∧ M.MemberSubset B D ∧
      ∀ s, M.mem s B → ∀ η : Env (rt_model_l X ⟨⟨ω, source.omega_mem⟩⟩) k,
        (∀ i, Rd_entry_d s (η.bound i).val (f i)) → Formula.satisfies η φ := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨_, hz⟩ := h.codes
  have models := h.components
  obtain ⟨o, _, hao⟩ := hz.2.1 a haJ
  obtain ⟨m, D', U', G, r, H, Q, hn, ha', hD', haU', hG, md⟩ := models a o hao
  have en := ha'.domain_eq_l hZF.1 ha
  subst m
  have eD := hZF.1.eq_of_same_members D' D (fun s => (hD' s).trans (hD s).symm)
  subst D'
  have eU := family.function a U' U haU' haU
  subst U'
  have ultra := family.at_l hZF.1 haU ha hD
  obtain ⟨v, hv, vs⟩ := ep_stage_embedding_l hZF source.omega h.toEg_graph_d h.diagram limit
    (h.toEp_graph_d.elementary_l hZFC source family coherent) model hao md.code
  obtain ⟨t, ht, ts⟩ := smap_comp_l I hZF hv he
  have read i : ∃ B, Rd_entry_d (f i) B r ∧ Rd_entry_d B (ρ.bound i).val t := by
    obtain ⟨E, ⟨u, B, hu, hfB, huE⟩, hEx⟩ := values i
    have hBH := (ep_at_read_l hz hao md.code.1).mp (h.toEp_graph_d.at_l (limit.projection.bound_l huE).1 hu)
    exact ⟨B, md.map.member_l I hZF.1 ultra.base hBH hfB,
      (ts B (ρ.bound i).val).mpr ⟨hBH, E, (vs B E).mpr ⟨hBH, u, hu, huE⟩, hEx⟩⟩
  obtain ⟨b, code⟩ := source.code
  have los := rs_formula_image_l hZF source.omega source.transitive code source.theory
    (source.uniform_l hZF hn hD) (source.space_mem_l hZF hn hD) ultra hG md target ht φ hφ f
    (fun i => (read i).elim fun _ h => md.map.projection.input_mem_of_pairMember h.1) ρ read
  refine los.trans (exists_congr fun B => and_congr_right fun _ => and_congr_right fun _ =>
    and_congr_right fun _ => ?_)
  constructor
  · intro holds s hs η entries
    exact (smem_formula_l I code ⟨⟨ω, source.omega_mem⟩⟩ φ η).mpr (holds s hs ⟨η.bound, η.free⟩ entries)
  · intro holds s hs η entries
    exact (smem_formula_l I code ⟨⟨ω, source.omega_mem⟩⟩ φ ⟨η.bound, η.free⟩).mp (holds s hs ⟨η.bound, η.free⟩ entries)

/-- 传递实现只负责最后的有界绝对性，全部商计算复用关系版本。 -/
theorem ep_delta_value_l (hZFC : M.Models ZFC) {ω κ K L X R F J O Z A p T V q c C W d N S e n D a U : M.Domain}
    (source : Ep_source_d (ZFC.models_zf_l hZFC) ω κ K X R) (family : Em_source_d ω κ L X F)
    (coherent : Ec_source_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ L X F)
    (h : Ep_system_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ L X R F J O Z A p T V) (limit : Di_limit_d A p T V q C W)
    (model : Smdl_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) c C W)
    (hN : M.TransitiveSet N) (target : Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) d N S)
    (he : Smap_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω c d C N e)
    (haJ : M.mem a J) (ha : Fn0_d n L a) (hD : Ep_space_d κ n D) (haU : Rd_entry_d a U F)
    {k} (φ : Formula 1 k) (hφ : φ.FreeClosed) (hd : φ.IsDelta0) (f : Fin k → M.Domain) (ρ : Env M k)
    (values : ∀ i, Ep_value_d q e a (f i) (ρ.bound i)) :
    Formula.satisfies ρ φ ↔ ∃ B, M.mem B X ∧ M.mem B U ∧ M.MemberSubset B D ∧
      ∀ s, M.mem s B → ∀ η : Env M k, (∀ i, Rd_entry_d s (η.bound i) (f i)) → Formula.satisfies η φ := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨y, hy⟩ := target.1.2.1
  let θ : Env (smdl_structure_l I (R := S) target.1.2.1) k :=
    ⟨fun i => ⟨ρ.bound i, (values i).elim fun _ h => he.1.1.output_mem_of_pairMember h.2⟩, fun _ => ⟨y, hy⟩⟩
  have read : Formula.satisfies θ φ ↔ Formula.satisfies ρ φ :=
    (smem_delta_image_l I target hN hd θ).trans (Formula.closed_env_l φ hφ rfl)
  have los := ep_formula_value_l hZFC source family coherent h limit model target.1 he haJ ha hD haU φ hφ f θ values
  refine read.symm.trans (los.trans (exists_congr fun B => and_congr_right fun _ => and_congr_right fun _ =>
    and_congr_right fun _ => ?_))
  constructor
  · intro holds s hs η entries
    have inside i : M.mem (η.bound i) X := by
      obtain ⟨E, rep, _⟩ := values i
      exact (rd_entry_transitive_l source.transitive (rep.source_l hZF family h limit).1 (entries i)).2
    let η' : Env (rt_model_l X ⟨⟨ω, source.omega_mem⟩⟩) k :=
      ⟨fun i => ⟨η.bound i, inside i⟩, fun _ => ⟨ω, source.omega_mem⟩⟩
    exact (Formula.closed_env_l φ hφ (ρ := image_env_l Subtype.val η') (η := η) rfl).mp
      ((rt_model_delta_l source.transitive _ hd η').mp (holds s hs η' entries))
  · intro holds s hs η entries
    exact (rt_model_delta_l source.transitive _ hd η).mpr
      (holds s hs ⟨fun i => (η.bound i).val, fun i => (η.free i).val⟩ entries)

/-- 在指定支撑上取常值初等嵌入，保留每个像的实际常值代表。 -/
theorem ep_value_constants_l (hZFC : M.Models ZFC) {ω κ K L X R F J O Z A p T V q c C W d N e n D a : M.Domain}
    (source : Ep_source_d (ZFC.models_zf_l hZFC) ω κ K X R) (family : Em_source_d ω κ L X F)
    (coherent : Ec_source_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ L X F)
    (h : Ep_system_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ L X R F J O Z A p T V) (limit : Di_limit_d A p T V q C W)
    (model : Smdl_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) c C W)
    (he : Smap_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω c d C N e)
    (haJ : M.mem a J) (ha : Fn0_d n L a) (hD : Ep_space_d κ n D) :
    let I := kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))
    ∃ b j, Smem_d I b X R ∧ Smap_d I ω b d X N j ∧ ∀ x y, Rd_entry_d x y j →
      ∃ f, M.mem f X ∧ Fn0_d D X f ∧ Rs_const_d D x f ∧ Ep_value_d q e a f y := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨_, hz⟩ := h.codes
  obtain ⟨o, _, hao⟩ := hz.2.1 a haJ
  obtain ⟨b, i, m, D', U, G, r, H, Q, code, hi, _, ha', hD', haU, hG, md, spec⟩ :=
    ep_constant_limit_l hZF source family h limit model (h.toEp_graph_d.elementary_l hZFC source family coherent) hao
  have en := ha'.domain_eq_l hZF.1 ha
  subst m
  have eD := hZF.1.eq_of_same_members D' D fun s => (hD' s).trans (hD s).symm
  subst D'
  obtain ⟨j, hj, js⟩ := smap_comp_l I hZF hi he
  refine ⟨b, j, code, hj, fun x y hxy => ?_⟩
  obtain ⟨_, E, hxE, hEy⟩ := (js x y).mp hxy
  obtain ⟨_, f, B, u, hf, hc, hfr, hu, huE⟩ := (spec x E).mp hxE
  exact ⟨f, ((hG f).mp hf).1, ((hG f).mp hf).2, hc,
    E, ⟨u, B, hu, md.map.representative_l I (family.at_l hZF.1 haU ha hD).base hfr, huE⟩, hEy⟩

/-- 任意源内自然数常值代表在传递实现中仍取原自然数。 -/
theorem ep_value_natural_l (hZFC : M.Models ZFC) {ω κ K L X R F J O Z A p T V q c C W d N S e n D a m f : M.Domain}
    (source : Ep_source_d (ZFC.models_zf_l hZFC) ω κ K X R) (family : Em_source_d ω κ L X F)
    (coherent : Ec_source_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ L X F)
    (h : Ep_system_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ L X R F J O Z A p T V) (limit : Di_limit_d A p T V q C W)
    (model : Smdl_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) c C W)
    (hN : M.TransitiveSet N) (target : Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) d N S)
    (he : Smap_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω c d C N e)
    (haJ : M.mem a J) (ha : Fn0_d n L a) (hD : Ep_space_d κ n D)
    (hm : M.mem m ω) (hf : Fn0_d D X f) (hc : Rs_const_d D m f) : Ep_value_d q e a f m := by
  let hZF := ZFC.models_zf_l hZFC
  obtain ⟨b, j, code, hj, constants⟩ := ep_value_constants_l hZFC source family coherent h limit model he haJ ha hD
  obtain ⟨g, _, hg, gc, value⟩ := constants m m
    (hj.natural_l hZF source.omega source.transitive hN code target source.omega_mem m hm)
  have eq := hg.ext_l hZF.1 hf fun s hs => ⟨m, gc s hs, hc s hs⟩
  exact eq ▸ value

end YesMetaZFC.SetTheory.LargeCardinal
