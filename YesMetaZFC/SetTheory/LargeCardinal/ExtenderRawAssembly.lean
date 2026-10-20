import YesMetaZFC.SetTheory.LargeCardinal.ExtenderRawComponent

/-! # 同一原关系源的全部有限支撑与初等定向极限

分量按规范结构码一次替换；全部支撑共用既有低层实现图。
测度、内部编号及过渡图均由实际源数据构造，再进入原定向极限构造。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal FilterZF
universe u
variable {M : Structure.{u}}

section Components
variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem er_components_l {ω c X R c' Y S q H N κ K L F R₀ Γ γ k : M.Domain}
  (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (mx : Smem_d I c X R)
  (theory : Sc_theory_d I ω X R) (collection : Sc_collection_d I ω X R)
  (model : Smdl_d I c' Y S) (hq : Smap_d I ω c c' X Y q)
  (small : Rr_small_d I Y S H)
  (closed : Rr_closed_d I Y S H)
  (owner : Ep_source_d hZF ω κ K N R₀) (hΓ : M.mem Γ N) (rank : Vr_d N γ Γ)
  (hγ : M.IsLimitOrdinal γ) (hκ : M.mem κ Γ) (fk : M.IsSetInjectionFromTo I k Γ Y)
  (image : ∀ z, Rd_entry_d z H S ↔ ∃ x, M.mem x Γ ∧ Rd_entry_d x z k)
  (pred : ∀ x z, Rd_entry_d x z k → ∀ w, Rd_entry_d w z S ↔ ∃ y, M.mem y x ∧ Rd_entry_d y w k)
  (family : Em_source_d ω κ L N F)
    {J : M.Domain} (indices : ∀ a, M.mem a J → Ei_d ω L a) :
    ∃ Z Q, Fn0_d J Q Z ∧ ∀ a o, Rd_entry_d a o Z → Er_component_d I ω κ L Y S F k a o := by
  let η : Env M 7 := ⟨Fin.cases k (Fin.cases F (Fin.cases S (Fin.cases Y (Fin.cases L (Fin.cases κ (fun _ => ω)))))), fun _ => ω⟩
  let φ : BinarySchema 7 := {
    body := er_component_m (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have sat a o : φ.denote η a o ↔ Er_component_d I ω κ L Y S F k a o := er_component_sat_l I hZF.1 ..
  have total a (ha : M.mem a J) : ∃ o, φ.denote η a o := by
    obtain ⟨n, hn, fa, _⟩ := indices a ha
    obtain ⟨U, haU⟩ := family.total n a hn fa
    obtain ⟨n', D, _, fa', space, measure⟩ := family.measure a U haU
    have eq := fa'.domain_eq_l hZF.1 fa
    subst n'
    have hD := (owner.rank_agree_l hZF hΓ rank hγ hκ n D D hn space (fun _ h => h)).mpr (owner.space_mem_l hZF hn space)
    obtain ⟨o, component⟩ := er_component_exists_l hZF hω hX mx theory collection model hq small closed
      (rank.transitive_l hZF owner.transitive hΓ) (owner.transitive Γ hΓ) fk image pred hn fa space haU hD measure
    exact ⟨o, (sat a o).mpr component⟩
  have unique a (_ : M.mem a J) b d (hb : φ.denote η a b) (hd : φ.denote η a d) :=
    ((sat a b).mp hb).unique_l I hZF.1 family (fn0_of_function_l (ZF.modelsKP hZF) fk.1) ((sat a d).mp hd)
  obtain ⟨Q, hQ⟩ := ZF.exists_functionalImageOn hZF φ η J total unique
  obtain ⟨Z, hz, spec⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ η total unique
    (fun a o ha ho => (hQ o).mpr ⟨a, ha, ho⟩)
  exact ⟨Z, Q, fn0_of_function_l (ZF.modelsKP hZF) hz, fun a o hao => (sat a o).mp ((spec a o).mp hao).2⟩

end Components

section Maps
variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem er_component_map_l {ω c X R c' Y S q H N κ K L F R₀ Γ γ k : M.Domain}
  (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (mx : Smem_d I c X R)
  (theory : Sc_theory_d I ω X R) (collection : Sc_collection_d I ω X R)
  (model : Smdl_d I c' Y S) (hq : Smap_d I ω c c' X Y q)
  (small : Rr_small_d I Y S H)
  (closed : Rr_closed_d I Y S H)
  (owner : Ep_source_d hZF ω κ K N R₀) (hΓ : M.mem Γ N) (rank : Vr_d N γ Γ)
  (hγ : M.IsLimitOrdinal γ) (fk : M.IsSetInjectionFromTo I k Γ Y)
  (image : ∀ z, Rd_entry_d z H S ↔ ∃ x, M.mem x Γ ∧ Rd_entry_d x z k)
  (pred : ∀ x z, Rd_entry_d x z k → ∀ w, Rd_entry_d w z S ↔ ∃ y, M.mem y x ∧ Rd_entry_d y w k)
  (family : Em_source_d ω κ L N F) (coherent : Ec_source_d I ω κ L N F)
    {a b o₀ o₁ m n r : M.Domain}
    (hm : M.mem m ω) (hn : M.mem n ω) (fr : Fn0_d m n r) (fb : Fn0_d n L b)
    (inj : ∀ i j x, Rd_entry_d i x b → Rd_entry_d j x b → i = j) (fra : Cp0_d m n L r b a)
    (first : Er_component_d I ω κ L Y S F k a o₀) (last : Er_component_d I ω κ L Y S F k b o₁) :
    ∃ j C₀ T₀ C₁ T₁, Smdl_d I o₀ C₀ T₀ ∧ Smdl_d I o₁ C₁ T₁ ∧ Smap_d I ω o₀ o₁ C₀ C₁ j ∧
      (∀ B C, Rd_entry_d B C j ↔ M.mem B C₀ ∧ M.mem C C₁ ∧ Ep_arrow_d ω κ L Y a b B C) ∧
      (∀ B C, Rd_entry_d B C j → Ep_lift_d ω κ L Y a b B C) ∧
      ∃ i D, Ep_space_d κ m D ∧ Smap_d I ω c' o₀ Y C₀ i ∧ ∀ x B, Rd_entry_d x B i ↔
        M.mem x Y ∧ M.mem B C₀ ∧ ∃ f, Fn0_d D Y f ∧ M.mem f B ∧ Rs_const_d D x f := by
  obtain ⟨m', D, U, d, u, G₀, p₀, C₀, T₀, _, fa, ds, haU, hDd, hu, hG₀, model₀⟩ := first
  obtain ⟨n', E, V, e, v, G₁, p₁, C₁, T₁, _, fb', es, hbV, hEe, hv, hG₁, model₁⟩ := last
  have eq := fa.domain_eq_l hZF.1 fra.1
  subst m'
  have eq := fb'.domain_eq_l hZF.1 fb
  subst n'
  have low := rank.transitive_l hZF owner.transitive hΓ
  have ext : Rf_ext_d I Y S := hq.extensional_l hZF hω mx.1 model (rf_ext_mem_l I hZF.1 hX mx)
  have prepare {D U d t G o p C T} (hDd : Rd_entry_d D d k) (ht : M.IsRestrictionOf I t k D)
      (hG : Rc_family_d I Y S D d t G) (quotient : Rp_model_d I D Y U S o G p C T) (measure : Sf_ultra_d N D U) :
      ∃ P V, Rt_source_d I Y S D t P ∧ M.MemberSubset P N ∧ Rel_ultra_d D P V ∧
        (∀ A, M.mem A V ↔ M.mem A P ∧ M.mem A U) ∧ Rp_model_d I D Y V S o G p C T := by
    obtain ⟨d', t', P, V, hDd', _, ht', ft, domain, hP, inN, ultra, restrict⟩ :=
      hq.measure_raw_l I hZF hω hX mx theory model closed low (owner.transitive Γ hΓ) fk image pred
        (fk.1.input_mem_of_pairMember hDd) measure
    have eq := fk.1.1.2 D d' d hDd' hDd
    subst d'
    have eq := ht'.1.eq_of_pairMember_iff hZF.1 ht.1 (fun s x => (ht'.2 s x).trans (ht.2 s x).symm)
    subst t'
    have functions := (rc_family_native_l I model.2.1 (ext.native_l I model.2.1)
      ⟨d, fk.1.output_mem_of_pairMember hDd⟩ (fn0_of_function_l (ZF.modelsKP hZF) ft)).mp hG
    exact ⟨P, V, hP, inN, ultra, restrict, rc_restrict_model_l hZF hω hX mx theory model hq
      ⟨d, fk.1.output_mem_of_pairMember hDd⟩ (fn0_of_function_l (ZF.modelsKP hZF) ft) domain hP inN measure restrict
      (fun g hg => by obtain ⟨_, _, f, _, decode⟩ := (functions g).mp hg; exact ⟨f, decode⟩) quotient⟩
  obtain ⟨P, U', hP, inN, ultra, us, model₀'⟩ := prepare hDd hu hG₀ model₀ (family.at_l hZF.1 haU fa ds)
  obtain ⟨Q, V', hQ, _, ultra', vs, model₁'⟩ := prepare hEe hv hG₁ model₁ (family.at_l hZF.1 hbV fb es)
  let d' : (smdl_structure_l I (R := S) model.2.1).Domain := ⟨d, fk.1.output_mem_of_pairMember hDd⟩
  let e' : (smdl_structure_l I (R := S) model.2.1).Domain := ⟨e, fk.1.output_mem_of_pairMember hEe⟩
  obtain ⟨μ₀, f₀, small₀⟩ := (small d d'.property ((image d).mpr ⟨D, fk.1.input_mem_of_pairMember hDd, hDd⟩)).index_l I model.2.1 d'
  obtain ⟨μ₁, f₁, small₁⟩ := (small e e'.property ((image e).mpr ⟨E, fk.1.input_mem_of_pairMember hEe, hEe⟩)).index_l I model.2.1 e'
  have ft (D d t) (hDd : Rd_entry_d D d k) (ht : M.IsRestrictionOf I t k D) :=
    fn0_of_function_l (ZF.modelsKP hZF) (ht.isSetFunctionFromTo fk.1 (low D (fk.1.input_mem_of_pairMember hDd)))
  obtain ⟨_, _, j, _, _, _, _, _, embed, _, spec, lift, i, _, hi, _, ci, _, _⟩ :=
    ep_raw_map_l hZFC hω hX mx theory collection model hq owner hΓ rank hγ fk pred d' e' μ₀ f₀ μ₁ f₁ hDd hEe hu hv
      small₀ small₁ hP hQ inN ultra ultra' us vs coherent hm hn fr fb fra haU hbV ds es inj
      ((rc_family_native_l I model.2.1 (ext.native_l I model.2.1) d' (ft D d u hDd hu)).mp hG₀)
      ((rc_family_native_l I model.2.1 (ext.native_l I model.2.1) e' (ft E e v hEe hv)).mp hG₁) model₀' model₁'
  refine ⟨j, C₀, T₀, C₁, T₁, model₀.code, model₁.code, embed, spec, lift, i, D, ds, hi, fun x B => ?_⟩
  constructor
  · intro hxB
    obtain ⟨hx, f, hf, fc, fp⟩ := (ci x B).mp hxB
    exact ⟨hx, hi.1.1.output_mem_of_pairMember hxB, f, model₀'.map.functions f hf, model₀'.map.representative_l I ultra.base fp, fc⟩
  · rintro ⟨hx, hB, f, _, hf, fc⟩
    have fp := model₀'.map.member_l I hZF.1 ultra.base hB hf
    exact (ci x B).mpr ⟨hx, f, model₀'.map.projection.input_mem_of_pairMember fp, fc, fp⟩

end Maps
end YesMetaZFC.SetTheory.LargeCardinal
