import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawProjection
import YesMetaZFC.Model.SetTheory.ReducedPower.RelationCopyPull
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawCoherence
import YesMetaZFC.Model.SetTheory.Reflection.ZfcTransfer
import YesMetaZFC.SetTheory.LargeCardinal.Extender.Ultrapower
import YesMetaZFC.SetTheory.LargeCardinal.Extender.Trace
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawOwnedCopy
import YesMetaZFC.SetTheory.Collapse.RelationRealization
import YesMetaZFC.Model.SetTheory.Embedding.Relative
import YesMetaZFC.Model.SetTheory.Source.RankSizeInitial
import YesMetaZFC.Model.SetTheory.Relations.Hierarchy
import YesMetaZFC.Model.SetTheory.Relations.LayerSeparation

/-! # 全部原关系支撑分量的规范结构码

定义域坐标取同一低层实现的限制；代表族由内部函数码唯一决定。
因此结构码唯一，可用替换统一装配，不逐支撑选择商模型。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal FilterZF
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def Er_component_d (ω κ L Y S F k a c : M.Domain) : Prop := ∃ n D U d t G p C T,
  M.mem n ω ∧ Fn0_d n L a ∧ Ep_space_d κ n D ∧ Rd_entry_d a U F ∧ Rd_entry_d D d k ∧
    M.IsRestrictionOf I t k D ∧ Rc_family_d I Y S D d t G ∧ Rp_model_d I D Y U S c G p C T

structure Er_system_d (ω κ L Y S F k J O Z A p T V : M.Domain) : Prop
    extends Eg_graph_d ω κ L Y J O Z A p T V where
  components : ∀ a c, Rd_entry_d a c Z → Er_component_d I ω κ L Y S F k a c
  diagram : Di_system_d J O A p T V
  representatives : ∀ u v a b B C, KPair_d M u a B → KPair_d M v b C → Rd_entry_d u v T →
    Ep_lift_d ω κ L Y a b B C


def er_component_m {n} (ω κ L Y S F k a c : Term n) : Formula 1 n := set[n] ⟪
  ∃ m D U d t G p C T, m ∈ ⌜ω⌝ₛ ∧ ⌜fn0_m⌝ₚ(m, ⌜L⌝ₛ, ⌜a⌝ₛ) ∧ ⌜ep_space_m⌝ₚ(⌜κ⌝ₛ, m, D) ∧
    ⌜rd_entry0_m⌝ₚ(⌜a⌝ₛ, U, ⌜F⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(D, d, ⌜k⌝ₛ) ∧
    ⌜Formula.isRestriction kpair_convention_l⌝ₚ(t, ⌜k⌝ₛ, D) ∧
    ⌜rc_family_m⌝ₚ(⌜Y⌝ₛ, ⌜S⌝ₛ, D, d, t, G) ∧
    ⌜rp_model_m (𝒞 := kpair_convention_l)⌝ₚ(D, ⌜Y⌝ₛ, U, ⌜S⌝ₛ, ⌜c⌝ₛ, G, p, C, T)⟫
derive_free_closed er_component_m

theorem er_component_sat_l (hE : Extensional M) {n} (ρ : Env M n) (ω κ L Y S F k a c : Term n) :
    Formula.satisfies ρ (er_component_m ω κ L Y S F k a c) ↔
      Er_component_d I (ω.eval ρ) (κ.eval ρ) (L.eval ρ) (Y.eval ρ) (S.eval ρ) (F.eval ρ) (k.eval ρ) (a.eval ρ) (c.eval ρ) := by
  simp only [er_component_m, Er_component_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, fn0_sat_l hE, ep_space_sat_l hE, rd_entry0_sat_l hE,
    Formula.satisfies_isRestriction_iff I, rc_family_sat_l I hE, rp_model_sat_l I hE, Definitional.Term.eval_weaken]; rfl

theorem Er_component_d.unique_l (hE : Extensional M) {ω κ L N Y S F k a c d Γ : M.Domain}
    (family : Em_source_d ω κ L N F) (fk : Fn0_d Γ Y k)
    (h : Er_component_d I ω κ L Y S F k a c) (g : Er_component_d I ω κ L Y S F k a d) : c = d := by
  obtain ⟨n, D, U, x, t, G, p, C, T, _, fa, space, haU, hDx, ht, hG, model⟩ := h
  obtain ⟨n', D', U', x', t', G', p', C', T', _, fa', space', haU', hDx', ht', hG', model'⟩ := g
  have eq := fa'.domain_eq_l hE fa
  subst n'
  have eq := hE.eq_of_same_members D' D (fun s => (space' s).trans (space s).symm)
  subst D'
  have eq := family.function a U' U haU' haU
  subst U'
  have eq := fk.2.2 D (fk.bound_l hDx).1 x' (fk.bound_l hDx').2 x (fk.bound_l hDx).2 hDx' hDx
  subst x'
  have eq := ht'.1.eq_of_pairMember_iff hE ht.1 (fun s y => (ht'.2 s y).trans (ht.2 s y).symm)
  subst t'
  have eq := hE.eq_of_same_members G' G (fun f => (hG' f).trans (hG f).symm)
  subst G'
  exact model.unique_l I hE model'

section Construction
variable (hZF : M.Models ZF)
local notation "Kp" => kp_pair_l (ZF.modelsKP hZF)

theorem Er_system_d.model_l {ω κ L Y S F k J O Z A p T V a B : M.Domain}
    (h : Er_system_d Kp ω κ L Y S F k J O Z A p T V) (hat : Ep_at_d Z a B) :
    ∃ o C W, Rd_entry_d a o Z ∧ Er_component_d Kp ω κ L Y S F k a o ∧ Smdl_d Kp o C W ∧ M.mem B C := by
  obtain ⟨o, C, W, hao, pair, hB⟩ := hat
  have component := h.components a o hao
  obtain ⟨_, _, _, _, _, _, _, C', W', _, _, _, _, _, _, _, model⟩ := component
  obtain ⟨rfl, rfl⟩ := kpair_injective_l M pair model.code.1
  exact ⟨o, C, W, hao, h.components a o hao, model.code, hB⟩

theorem er_component_exists_l {ω c X R c' Y S q H Γ k N κ L F a n D U : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (mx : Smem_d Kp c X R)
    (theory : Sc_theory_d Kp ω X R) (collection : Sc_collection_d Kp ω X R)
    (model : Smdl_d Kp c' Y S) (hq : Smap_d Kp ω c c' X Y q)
    (small : Rr_small_d Kp Y S H)
    (closed : Rr_closed_d Kp Y S H)
    (hΓ : M.TransitiveSet Γ) (inside : M.MemberSubset Γ N) (fk : M.IsSetInjectionFromTo Kp k Γ Y)
    (image : ∀ z, Rd_entry_d z H S ↔ ∃ x, M.mem x Γ ∧ Rd_entry_d x z k)
    (pred : ∀ x z, Rd_entry_d x z k → ∀ w, Rd_entry_d w z S ↔ ∃ y, M.mem y x ∧ Rd_entry_d y w k)
    (hn : M.mem n ω) (fa : Fn0_d n L a) (space : Ep_space_d κ n D) (haU : Rd_entry_d a U F)
    (hD : M.mem D Γ) (measure : Sf_ultra_d N D U) : ∃ o, Er_component_d Kp ω κ L Y S F k a o := by
  obtain ⟨d, t, P, V, hDd, hdH, ht, ft, domain, hP, inN, ultra, restrict⟩ :=
    hq.measure_raw_l Kp hZF hω mx.1 theory model closed hΓ inside fk image pred hD measure
  have hd := fk.1.output_mem_of_pairMember hDd
  have ext : Rf_ext_d Kp Y S := hq.extensional_l hZF hω mx.1 model (rf_ext_mem_l Kp hZF.1 hX mx)
  have collect := (sc_collection_iff_l Kp hZF hω mx.1 model
    (smem_ext_l Kp mx.1 mx.2 hX hZF.1) (ext.native_l Kp model.2.1) hq).mp collection
  obtain ⟨μ, e, index⟩ := (small d hd hdH).index_l Kp model.2.1 ⟨d, hd⟩
  obtain ⟨G, o, p, C, T, _, _, quotient, _, functions, _⟩ := rc_successor_l hZF hω
    (rf_ext_mem_l Kp hZF.1 hX mx) mx.1 theory model hq
    ⟨d, hd⟩ (collect model.2.1 ⟨d, hd⟩ μ e index) (fn0_of_function_l (ZF.modelsKP hZF) ft) domain hP measure.base measure.proper
    (fun A B ha hb => measure.upward A B ha (inN B hb) (ultra.field.bounds B hb)) ultra restrict
  exact ⟨o, n, D, U, d, t, G, p, C, T, hn, fa, space, haU, hDd, ht,
    (rc_family_native_l Kp model.2.1 (ext.native_l Kp model.2.1) ⟨d, hd⟩ (fn0_of_function_l (ZF.modelsKP hZF) ft)).mpr functions, quotient⟩

end Construction
end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 同一原关系源的全部有限支撑与初等定向极限

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

theorem er_components_l {ω c X R c' Y S q H N κ L F Γ k : M.Domain}
  (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (mx : Smem_d I c X R)
  (theory : Sc_theory_d I ω X R) (collection : Sc_collection_d I ω X R)
  (model : Smdl_d I c' Y S) (hq : Smap_d I ω c c' X Y q)
  (small : Rr_small_d I Y S H)
  (closed : Rr_closed_d I Y S H)
  (fs : Fs_read_d ω Γ) (inside : M.MemberSubset Γ N)
  (hκ : M.mem κ Γ) (fk : M.IsSetInjectionFromTo I k Γ Y)
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
    obtain ⟨D', hD, space'⟩ := fs.spaces κ n hκ hn
    have eq := hZF.1.eq_of_same_members D' D (fun s => (space' s).trans (space s).symm)
    subst D'
    obtain ⟨o, component⟩ := er_component_exists_l hZF hω hX mx theory collection model hq small closed
      fs.transitive inside fk image pred hn fa space haU hD measure
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

theorem er_component_map_l {ω c X R c' Y S q H N κ L F Γ cΓ RΓ k : M.Domain}
  (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (mx : Smem_d I c X R)
  (theory : Sc_theory_d I ω X R) (collection : Sc_collection_d I ω X R)
  (model : Smdl_d I c' Y S) (hq : Smap_d I ω c c' X Y q)
  (small : Rr_small_d I Y S H)
  (closed : Rr_closed_d I Y S H)
  (fs : Fs_read_d ω Γ) (mg : Smem_d I cΓ Γ RΓ) (tg : Sc_theory_d I ω Γ RΓ)
  (inside : M.MemberSubset Γ N) (hκ : M.mem κ Γ) (fk : M.IsSetInjectionFromTo I k Γ Y)
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
  have low := fs.transitive
  have ext : Rf_ext_d I Y S := hq.extensional_l hZF hω mx.1 model (rf_ext_mem_l I hZF.1 hX mx)
  have prepare {D U d t G o p C T} (hDd : Rd_entry_d D d k) (ht : M.IsRestrictionOf I t k D)
      (hG : Rc_family_d I Y S D d t G) (quotient : Rp_model_d I D Y U S o G p C T) (measure : Sf_ultra_d N D U) :
      ∃ P V, Rt_source_d I Y S D t P ∧ M.MemberSubset P N ∧ Rel_ultra_d D P V ∧
        (∀ A, M.mem A V ↔ M.mem A P ∧ M.mem A U) ∧ Rp_model_d I D Y V S o G p C T := by
    obtain ⟨d', t', P, V, hDd', _, ht', ft, domain, hP, inN, ultra, restrict⟩ :=
      hq.measure_raw_l I hZF hω mx.1 theory model closed low inside fk image pred
        (fk.1.input_mem_of_pairMember hDd) measure
    have eq := fk.1.1.2 D d' d hDd' hDd
    subst d'
    have eq := ht'.1.eq_of_pairMember_iff hZF.1 ht.1 (fun s x => (ht'.2 s x).trans (ht.2 s x).symm)
    subst t'
    have functions := (rc_family_native_l I model.2.1 (ext.native_l I model.2.1)
      ⟨d, fk.1.output_mem_of_pairMember hDd⟩ (fn0_of_function_l (ZF.modelsKP hZF) ft)).mp hG
    exact ⟨P, V, hP, inN, ultra, restrict, rc_restrict_model_l hZF hω
      (rf_ext_mem_l I hZF.1 hX mx) mx.1 theory model hq
      ⟨d, fk.1.output_mem_of_pairMember hDd⟩ (fn0_of_function_l (ZF.modelsKP hZF) ft) domain hP measure.base
      (fun A B ha hb => measure.upward A B ha (inN B hb) (ultra.field.bounds B hb)) restrict
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
    ep_raw_map_l hZFC hω hX mx theory collection model hq fs mg tg hκ fk pred d' e' μ₀ f₀ μ₁ f₁ hDd hEe hu hv
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

/-! ## 全部原关系支撑的实际初等极限

规范分量图、既有坐标过渡和标签同构共同给出一个实际定向系统。
原源的常值图经空支撑分量进入极限，并返回同一原始模型的复合初等图。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal FilterZF
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem er_ultrapower_l {ω c X R c' Y S q H N κ L F Γ cΓ RΓ k : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (mx : Smem_d I c X R)
    (theory : Sc_theory_d I ω X R) (collection : Sc_collection_d I ω X R)
    (model : Smdl_d I c' Y S) (hq : Smap_d I ω c c' X Y q)
    (small : Rr_small_d I Y S H)
    (closed : Rr_closed_d I Y S H)
    (fs : Fs_read_d ω Γ) (mg : Smem_d I cΓ Γ RΓ) (tg : Sc_theory_d I ω Γ RΓ)
    (inside : M.MemberSubset Γ N) (hκ : M.mem κ Γ) (fk : M.IsSetInjectionFromTo I k Γ Y)
    (image : ∀ z, Rd_entry_d z H S ↔ ∃ x, M.mem x Γ ∧ Rd_entry_d x z k)
    (pred : ∀ x z, Rd_entry_d x z k → ∀ w, Rd_entry_d w z S ↔ ∃ y, M.mem y x ∧ Rd_entry_d y w k)
    (family : Em_source_d ω κ L N F) (coherent : Ec_source_d I ω κ L N F) :
    ∃ J O Z A p T V r o C W i q', Er_system_d I ω κ L Y S F k J O Z A p T V ∧
      Di_limit_d A p T V r C W ∧ Smdl_d I o C W ∧ Di_elementary_d I ω O A p T V ∧
      Smap_d I ω c' o Y C i ∧ Smap_d I ω c o X C q' ∧
      (Zc_model_d I ω c X R → Zc_model_d I ω o C W) ∧
      (∀ x z, Rd_entry_d x z q' ↔ M.mem x X ∧ ∃ y, Rd_entry_d x y q ∧ Rd_entry_d y z i) ∧
      ∃ a D, (∀ z, ¬ M.mem z a) ∧ Ep_space_d κ a D ∧
        ∀ x E, Rd_entry_d x E i → ∃ B f u, Fn0_d D Y f ∧ M.mem f B ∧ Rs_const_d D x f ∧
          KPair_d M u a B ∧ Rd_entry_d u E r := by
  obtain ⟨J, O, indices, order, os⟩ := ei_order_l hZF hω
  obtain ⟨Z, Q, hz, components⟩ := er_components_l hZF hω hX mx theory collection model hq small closed
    fs inside hκ fk image pred family (fun a ha => (indices a).mp ha)
  obtain ⟨A, p, T, V, graph⟩ := eg_graphs_l hZF (κ := κ) (X := Y) order os indices hz
  have maps {a b o₀ o₁ m n r : M.Domain} := er_component_map_l hZFC hω hX mx theory collection model hq small closed
    fs mg tg inside hκ fk image pred family coherent (a := a) (b := b) (o₀ := o₀) (o₁ := o₁) (m := m) (n := n) (r := r)
  have transition : Eg_transition_d I ω κ L Y O Z := by
    intro a b hab
    obtain ⟨ha, hb, t, m, n, hm, hn, ft, fb, fta⟩ := (os a b).mp hab
    obtain ⟨c₀, _, hac⟩ := hz.2.1 a ha
    obtain ⟨c₁, _, hbd⟩ := hz.2.1 b hb
    obtain ⟨_, _, _, inj⟩ := (indices b).mp hb
    obtain ⟨j, C₀, T₀, C₁, T₁, mc₀, mc₁, embed, spec, lift, _⟩ :=
      maps hm hn ft fb inj fta (components a c₀ hac) (components b c₁ hbd)
    exact ⟨j, c₀, C₀, T₀, c₁, C₁, T₁, hac, hbd, mc₀, mc₁, embed, spec, lift⟩
  have reps a B (hat : Ep_at_d Z a B) : ∃ n, M.mem n ω ∧ Fn0_d n L a ∧
      (∃ f, M.mem f B) ∧ ∀ f, M.mem f B → Ep_fun_d κ Y n f := by
    obtain ⟨o, C, W, hao, pair, hB⟩ := hat
    obtain ⟨n, D, U, _, _, G, s, C', W', hn, fa, space, haU, _, _, functions, quotient⟩ := components a o hao
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M pair quotient.code.1
    have measure := (family.at_l hZF.1 haU fa space).base
    obtain ⟨f, hfp⟩ := (quotient.map.range B).mp hB
    exact ⟨n, hn, fa, ⟨f, quotient.map.representative_l I measure hfp⟩, fun g hg =>
      ⟨D, space, ((functions g).mp (quotient.map.projection.input_mem_of_pairMember
        (quotient.map.member_l I hZF.1 measure hB hg))).1⟩⟩
  obtain ⟨diagram, lifts⟩ := graph.system_l hZF hω reps transition
  have elementary := graph.elementary_l hZF hω transition
  obtain ⟨a, empty, haω⟩ := hω.1.1
  have fa : Fn0_d a L a := ⟨fun x hx => (empty x hx).elim, fun x hx => (empty x hx).elim, fun x hx => (empty x hx).elim⟩
  have inj i j x (h : Rd_entry_d i x a) (_ : Rd_entry_d j x a) : i = j := h.elim fun z hz => (empty z hz.2).elim
  have haJ := (indices a).mpr ⟨a, haω, fa, inj⟩
  obtain ⟨o₀, _, hao⟩ := hz.2.1 a haJ
  have aa : Fn0_d a a a := ⟨fun x hx => (empty x hx).elim, fun x hx => (empty x hx).elim, fun x hx => (empty x hx).elim⟩
  obtain ⟨_, C₀, T₀, _, _, mc₀, _, _, _, _, i₀, D, space, hi₀, const⟩ :=
    maps haω haω aa fa inj ⟨fa, fun x hx => (empty x hx).elim⟩ (components a o₀ hao) (components a o₀ hao)
  obtain ⟨B₀, hB₀⟩ := mc₀.2.1
  obtain ⟨u, pair⟩ := (I).total a B₀
  have hu := (graph.nodes u).mpr ⟨a, B₀, pair, o₀, C₀, T₀, hao, mc₀.1, hB₀⟩
  obtain ⟨o, r, C, W, limit, mc⟩ := di_model_exists_l hZF diagram ⟨u, hu⟩
  obtain ⟨v, hv, values⟩ := ep_stage_embedding_l hZF hω graph diagram limit elementary mc hao mc₀
  obtain ⟨i, hi, square⟩ := smap_comp_l I hZF hi₀ hv
  obtain ⟨q', hq', composition⟩ := smap_comp_l I hZF hq hi
  refine ⟨J, O, Z, A, p, T, V, r, o, C, W, i, q', ⟨graph, components, diagram, lifts⟩,
    limit, mc, elementary, hi, hq', (fun certificate => certificate.map_l hZF hω mc hq'),
    composition, a, D, empty, space, fun x E hxE => ?_⟩
  obtain ⟨_, B₁, hxB, hBE⟩ := (square x E).mp hxE
  obtain ⟨_, _, f, ff, hf, fc⟩ := (const x B₁).mp hxB
  obtain ⟨_, u, pair, huE⟩ := (values B₁ E).mp hBE
  exact ⟨B₁, f, u, ff, hf, fc, pair, huE⟩

/-- 原关系所属证书生成全部支撑及同一未坍塌极限，源和所属侧都可保留原关系。 -/
theorem It_local_d.raw_ultrapower_l {ω c X R c' Y S q Γ cΓ RΓ H k N T H₀ k₀ κ : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (mx : Smem_d I c X R)
    (theory : Sc_theory_d I ω X R) (collection : Sc_collection_d I ω X R)
    (model : Smdl_d I c' Y S) (hq : Smap_d I ω c c' X Y q)
    (layer : Rr_layer_d I Γ Y S H k) (closed : Rr_closed_d I Y S H) (small : Rr_small_d I Y S H)
    (owner : Rr_layer_d I Γ N T H₀ k₀) (oc : Rr_closed_d I N T H₀)
    (hN : (smdl_structure_l I (R := T) ⟨H₀, owner.member⟩).Models ZF)
    (fs : Fs_read_d ω Γ) (mg : Smem_d I cΓ Γ RΓ) (tg : Sc_theory_d I ω Γ RΓ)
    (w ξ ℓ f : (smdl_structure_l I (R := T) ⟨H₀, owner.member⟩).Domain)
    (hw : Rd_entry_d ω w.val k₀) (hκ : Rd_entry_d κ ξ.val k₀)
    (loc : It_local_d I w.val N T ξ.val ℓ.val f.val) :
    ∃ L F, (∀ x, M.mem x L ↔ M.mem x N ∧ Rd_entry_d x ℓ.val T) ∧
      Em_source_d ω κ L Γ F ∧ Ec_source_d I ω κ L Γ F ∧
      (∀ a U, Rd_entry_d a U F ↔ Er_measure_d I ω κ L N T f.val k₀ a U) ∧
      ∃ J O Z A p V W r o C Q j q', Er_system_d I ω κ L Y S F k J O Z A p V W ∧
        Di_limit_d A p V W r C Q ∧ Smdl_d I o C Q ∧ Di_elementary_d I ω O A p V W ∧
        Smap_d I ω c' o Y C j ∧ Smap_d I ω c o X C q' ∧
        (Zc_model_d I ω c X R → Zc_model_d I ω o C Q) ∧
        (∀ x z, Rd_entry_d x z q' ↔ M.mem x X ∧ ∃ y, Rd_entry_d x y q ∧ Rd_entry_d y z j) ∧
        ∃ a D, (∀ z, ¬ M.mem z a) ∧ Ep_space_d κ a D ∧
          ∀ x E, Rd_entry_d x E j → ∃ B g u, Fn0_d D Y g ∧ M.mem g B ∧ Rs_const_d D x g ∧
            KPair_d M u a B ∧ Rd_entry_d u E r := by
  obtain ⟨L, F, length, family, coherent, table⟩ :=
    loc.raw_family_l hZF owner oc hN hω fs (tg.algebra_l _ (ZF.modelsKP hZF) fs.transitive mg) w ξ ℓ f hw hκ
  refine ⟨L, F, length, family, coherent, table, ?_⟩
  exact er_ultrapower_l hZFC hω hX mx theory collection model hq small closed fs mg tg
    (fun _ h => h) (owner.injection.1.input_mem_of_pairMember hκ)
    layer.injection layer.image layer.predecessors family coherent

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原关系定向极限的完整有界代表覆盖

任意新成员与原常值先移到共同支撑，再在同一原子测度下规范化。
共同低层回收所得内部函数码，最终得到同一低层中的实际有界函数。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal FilterZF
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Er_system_d.bounded_l {ω c X R c' Y S q H N κ L F Γ k J O Z A p T V r C W
    A₀ b D₀ a₀ f₀ H₀ E : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (mx : Smem_d I c X R)
    (theory : Sc_theory_d I ω X R) (model : Smdl_d I c' Y S) (hq : Smap_d I ω c c' X Y q)
    (closed : Rr_closed_d I Y S H)
    (low : M.TransitiveSet Γ) (algebra : Sc_algebra_d Γ) (fk : M.IsSetInjectionFromTo I k Γ Y)
    (image : ∀ z, Rd_entry_d z H S ↔ ∃ x, M.mem x Γ ∧ Rd_entry_d x z k)
    (pred : ∀ x z, Rd_entry_d x z k → ∀ w, Rd_entry_d w z S ↔ ∃ y, M.mem y x ∧ Rd_entry_d y w k)
    (family : Em_source_d ω κ L N F) (system : Er_system_d I ω κ L Y S F k J O Z A p T V)
    (limit : Di_limit_d A p T V r C W) (hAb : Rd_entry_d A₀ b k)
    (ff₀ : Fn0_d D₀ Y f₀) (constant : Rs_const_d D₀ b f₀) (fv : Ep_repr_d r a₀ f₀ H₀)
    (edge : Rd_entry_d E H₀ W) :
    ∃ n a D f g, M.mem n ω ∧ M.mem a J ∧ Fn0_d n L a ∧ Ep_space_d κ n D ∧
      M.mem f Γ ∧ Fn0_d D A₀ f ∧ Cp0_d D Γ Y f k g ∧ Ep_repr_d r a g E := by
  obtain ⟨u, huE⟩ := (limit.range E).mp (limit.bounded E H₀ edge).1
  obtain ⟨v, B₀, pv, hfB₀, hvH⟩ := fv
  obtain ⟨a, w, z, hwa, hza, huw, hvz, hwz⟩ := (limit.relation u v E H₀ huE hvH).mp edge
  obtain ⟨P, pw, atP⟩ := system.toEg_graph_d.label_l hwa
  obtain ⟨Q, pz, atQ⟩ := system.toEg_graph_d.label_l hza
  obtain ⟨o, C₁, W₁, hao, component, mc, hPC⟩ := system.model_l hZF atP
  obtain ⟨_, hz⟩ := system.codes
  have hQC := (ep_at_read_l hz hao mc.1).mp atQ
  have rel := (ep_rel_read_l hz hao mc.1).mp ((system.toEg_graph_d.relation_l pw pz).mp hwz).2.2
  obtain ⟨n, D, U, d, t, G, s, C₂, W₂, hn, fa, space, haU, hDd, ht, functions, quotient⟩ := component
  obtain ⟨rfl, rfl⟩ := smdl_unique_l I quotient.code mc
  have measure := family.at_l hZF.1 haU fa space
  -- 原常值沿同一实际支撑箭头拉回，仍是新分量中的处处常值。
  obtain ⟨m, n', t₀, f', _, _, ft₀, fa', fta₀, hfQ, pull⟩ :=
    system.representatives v z a₀ a B₀ Q pv pz hvz f₀ hfB₀
  have eq := fa'.domain_eq_l hZF.1 fa
  subst n'
  obtain ⟨D', space₀, ff⟩ := pull.1
  have eq := ff.domain_eq_l hZF.1 ff₀
  subst D'
  have fc : Rs_const_d D b f' := by
    intro s hs
    obtain ⟨v, comp⟩ := cp0_exists_l (ZF.modelsKP hZF) ft₀ ((space s).mp hs)
    exact (pull.2.2 s v ((space s).mp hs) comp b).mpr (constant v ((space₀ v).mpr comp.1))
  have fp := quotient.map.member_l I hZF.1 measure.base hQC hfQ
  have ft := fn0_of_function_l (ZF.modelsKP hZF) (ht.isSetFunctionFromTo fk.1 (low D (fk.1.input_mem_of_pairMember hDd)))
  have domain s x (hsx : Rd_entry_d s x t) := (pred D d hDd x).mpr
    ⟨s, ((ht.2 s x).mp hsx).1, ((ht.2 s x).mp hsx).2⟩
  have ext : Rf_ext_d I Y S := hq.extensional_l hZF hω mx.1 model (rf_ext_mem_l I hZF.1 hX mx)
  let d' : (smdl_structure_l I (R := S) model.2.1).Domain := ⟨d, fk.1.output_mem_of_pairMember hDd⟩
  let b' : (smdl_structure_l I (R := S) model.2.1).Domain := ⟨b, fk.1.output_mem_of_pairMember hAb⟩
  have codes := (rc_family_native_l I model.2.1 (ext.native_l I model.2.1) d' ft).mp functions
  obtain ⟨g, hg, gp, bound, _⟩ := rc_bounded_representative_l hZF hω model ext
    (theory.map_l I hZF hω mx.1 model hq) d' ft domain
    measure.base measure.proper codes quotient ⟨b'.property, f', quotient.map.projection.input_mem_of_pairMember fp, fc, fp⟩ rel
  obtain ⟨f, hf, fn, comp⟩ := (rr_bounded_functions_l hZF model.2.1 ext closed low algebra
    fk image pred d' b' hDd hAb ht codes g).mp ⟨hg, bound⟩
  obtain ⟨E', _, hwE⟩ := limit.projection.2.1 w (system.projection.bound_l hwa).1
  have eq := limit.commute_l system.diagram huw huE hwE
  exact ⟨n, a, D, f, g, hn, (system.projection.bound_l hwa).2, fa, space, hf, fn, comp,
    w, P, pw, quotient.map.representative_l I measure.base gp, eq.symm ▸ hwE⟩

theorem Er_system_d.bound_mem_l {ω κ L N Y S F k J O Z A p T V r C W D₀ b a₀ f₀ H₀ a g E : M.Domain}
    (family : Em_source_d ω κ L N F) (system : Er_system_d I ω κ L Y S F k J O Z A p T V)
    (limit : Di_limit_d A p T V r C W) (hb : M.mem b Y)
    (ff₀ : Fn0_d D₀ Y f₀) (constant : Rs_const_d D₀ b f₀) (fv : Ep_repr_d r a₀ f₀ H₀)
    (bound : ∀ s y, Rd_entry_d s y g → Rd_entry_d y b S) (gv : Ep_repr_d r a g E) : Rd_entry_d E H₀ W := by
  obtain ⟨u, B, pu, hgB, huE⟩ := gv
  obtain ⟨v, B₀, pv, hfB₀, hvH⟩ := fv
  obtain ⟨c, w, z, hwc, hzc, huw, hvz⟩ := system.diagram.common_l (limit.projection.bound_l huE).1 (limit.projection.bound_l hvH).1
  obtain ⟨P, pw, atP⟩ := system.toEg_graph_d.label_l hwc
  obtain ⟨Q, pz, atQ⟩ := system.toEg_graph_d.label_l hzc
  obtain ⟨o, C₁, W₁, hco, component, mc, hPC⟩ := system.model_l hZF atP
  obtain ⟨_, hz⟩ := system.codes
  have hQC := (ep_at_read_l hz hco mc.1).mp atQ
  obtain ⟨n, D, U, _, _, G, s, C₂, W₂, _, fc, space, hcU, _, _, _, quotient⟩ := component
  obtain ⟨rfl, rfl⟩ := smdl_unique_l I quotient.code mc
  have measure := (family.at_l hZF.1 hcU fc space).base
  obtain ⟨m, n', t, g', _, _, ft, fc', _, hgP, pg⟩ := system.representatives u w a c B P pu pw huw g hgB
  have eq := fc'.domain_eq_l hZF.1 fc
  subst n'
  obtain ⟨l, n', t₀, f', _, _, ft₀, fc', _, hfQ, pf⟩ := system.representatives v z a₀ c B₀ Q pv pz hvz f₀ hfB₀
  have eq := fc'.domain_eq_l hZF.1 fc
  subst n'
  obtain ⟨D', ds₀, ff⟩ := pf.1
  have eq := ff.domain_eq_l hZF.1 ff₀
  subst D'
  have gp := quotient.map.member_l I hZF.1 measure hPC hgP
  have fp := quotient.map.member_l I hZF.1 measure hQC hfQ
  have fg := quotient.map.functions g' (quotient.map.projection.input_mem_of_pairMember gp)
  have relation := (quotient.relation g' f' P Q gp fp).mpr ⟨D, measure.top, fun s hs => by
    have sf := (space s).mp hs
    obtain ⟨v, tv⟩ := cp0_exists_l (ZF.modelsKP hZF) ft sf
    obtain ⟨v₀, tv₀⟩ := cp0_exists_l (ZF.modelsKP hZF) ft₀ sf
    obtain ⟨y, hy, hsy⟩ := fg.2.1 s hs
    exact ⟨y, hy, b, hb, hsy, (pf.2.2 s v₀ sf tv₀ b).mpr (constant v₀ ((ds₀ v₀).mpr tv₀.1)),
      bound v y ((pg.2.2 s v sf tv y).mp hsy)⟩⟩
  exact (limit.relation u v E H₀ huE hvH).mpr ⟨c, w, z, hwc, hzc, huw, hvz,
    (system.toEg_graph_d.relation_l pw pz).mpr ⟨(system.projection.bound_l hwc).1,
      (system.projection.bound_l hzc).1, (ep_rel_read_l hz hco mc.1).mpr relation⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 共同有界代表在原关系极限中的实际求值

共同低层中的函数先与实现图复合，再读取同一规范商与极限投影。
同支撑原子方程始终使用原测度。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal FilterZF
universe u
variable {M : Structure.{u}}

def Er_value_d (κ Γ Y k r u E : M.Domain) : Prop := ∃ a f n D g,
  KPair_d M u a f ∧ Ep_space_d κ n D ∧ Fn0_d D Γ f ∧ Cp0_d D Γ Y f k g ∧ Ep_repr_d r a g E

def er_value_m {d} (κ Γ Y k r u E : Term d) : Formula 1 d := set[d] ⟪
  ∃ a f n D g, ⌜kpair0_m⌝ₚ(⌜u⌝ₛ, a, f) ∧ ⌜ep_space_m⌝ₚ(⌜κ⌝ₛ, n, D) ∧
    ⌜fn0_m⌝ₚ(D, ⌜Γ⌝ₛ, f) ∧ ⌜cp0_m⌝ₚ(D, ⌜Γ⌝ₛ, ⌜Y⌝ₛ, f, ⌜k⌝ₛ, g) ∧ ⌜ep_repr_m⌝ₚ(⌜r⌝ₛ, a, g, ⌜E⌝ₛ)⟫
derive_free_closed er_value_m

theorem er_value_sat_l (hE : Extensional M) {d} (ρ : Env M d) (κ Γ Y k r u E : Term d) :
    Formula.satisfies ρ (er_value_m κ Γ Y k r u E) ↔
      Er_value_d (κ.eval ρ) (Γ.eval ρ) (Y.eval ρ) (k.eval ρ) (r.eval ρ) (u.eval ρ) (E.eval ρ) := by
  simp only [er_value_m, Er_value_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    kpair0_sat_l hE, ep_space_sat_l hE, fn0_sat_l hE, cp0_sat_l hE, ep_repr_sat_l hE, Definitional.Term.eval_weaken]; rfl

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem er_repr_atoms_l {ω κ L N Y S F k J O Z A p T V r C W a f g E H U : M.Domain}
    (family : Em_source_d ω κ L N F) (h : Er_system_d I ω κ L Y S F k J O Z A p T V)
    (limit : Di_limit_d A p T V r C W) (haU : Rd_entry_d a U F)
    (he : Ep_repr_d r a f E) (hh : Ep_repr_d r a g H) :
    (E = H ↔ Rp_eq_d Y U f g) ∧ (Rd_entry_d E H W ↔ Rp_rel_d I Y U S f g) := by
  obtain ⟨u, B, hu, hf, huE⟩ := he
  obtain ⟨v, D, hv, hg, hvH⟩ := hh
  have huA := (limit.projection.bound_l huE).1
  have hvA := (limit.projection.bound_l hvH).1
  have hua := (h.index u a B hu).mpr huA
  have hva := (h.index v a D hv).mpr hvA
  obtain ⟨_, hz⟩ := h.codes
  obtain ⟨o, Q, R, hao, component, model, hBQ⟩ := h.model_l hZF (h.toEg_graph_d.at_l huA hu)
  have hDQ := (ep_at_read_l hz hao model.1).mp (h.toEg_graph_d.at_l hvA hv)
  obtain ⟨n, Q₀, U₀, _, _, G, s, Q', R', _, fa, space, haU₀, _, _, _, md⟩ := component
  obtain ⟨rfl, rfl⟩ := smdl_unique_l I md.code model
  have eq := family.function a U₀ U haU₀ haU
  subst U₀
  have measure := (family.at_l hZF.1 haU fa space).base
  have fp := md.map.member_l I hZF.1 measure hBQ hf
  have gp := md.map.member_l I hZF.1 measure hDQ hg
  have same : u = v ↔ B = D := ⟨fun eq => (kpair_injective_l M (eq ▸ hu) hv).2,
    fun eq => kpair_unique_l M hZF.1 (eq ▸ hu) hv⟩
  refine ⟨(limit.kernel u v E H huE hvH).trans ((h.diagram.eq_at_l hua hva).trans
    (same.trans (rp_kernel_l I hZF.1 measure md.map fp gp))), ?_⟩
  exact (limit.relation u v E H huE hvH).trans
    ((h.diagram.rel_at_l hua hva (h.diagram.identity u huA) (h.diagram.identity v hvA)).trans
      ((h.toEg_graph_d.relation_l hu hv).trans
        ((and_congr_right fun _ => and_congr_right fun _ => ep_rel_read_l hz hao model.1).trans
          ((and_iff_right huA).trans ((and_iff_right hvA).trans (md.relation f g B D fp gp))))))

theorem Er_system_d.bounded_value_l {ω c X R c' Y S q H N κ L F Γ k J O Z A p T V r C W
    A₀ b n a D f : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (mx : Smem_d I c X R)
    (model : Smdl_d I c' Y S) (hq : Smap_d I ω c c' X Y q)
    (closed : Rr_closed_d I Y S H)
    (low : M.TransitiveSet Γ) (algebra : Sc_algebra_d Γ) (fk : M.IsSetInjectionFromTo I k Γ Y)
    (image : ∀ z, Rd_entry_d z H S ↔ ∃ x, M.mem x Γ ∧ Rd_entry_d x z k)
    (pred : ∀ x z, Rd_entry_d x z k → ∀ w, Rd_entry_d w z S ↔ ∃ y, M.mem y x ∧ Rd_entry_d y w k)
    (family : Em_source_d ω κ L N F) (system : Er_system_d I ω κ L Y S F k J O Z A p T V)
    (limit : Di_limit_d A p T V r C W) (hAb : Rd_entry_d A₀ b k)
    (ha : M.mem a J) (fa : Fn0_d n L a) (space : Ep_space_d κ n D) (hf : M.mem f Γ) (ff : Fn0_d D A₀ f) :
    ∃ g E, Cp0_d D Γ Y f k g ∧ Ep_repr_d r a g E := by
  obtain ⟨_, hz⟩ := system.codes
  obtain ⟨o, _, hao⟩ := hz.2.1 a ha
  obtain ⟨n', D', U, d, t, G, s, C₁, W₁, _, fa', space', haU, hDd, ht, functions, quotient⟩ := system.components a o hao
  have eq := fa'.domain_eq_l hZF.1 fa
  subst n'
  have eq := hZF.1.eq_of_same_members D' D (fun s => (space' s).trans (space s).symm)
  subst D'
  have ft := fn0_of_function_l (ZF.modelsKP hZF) (ht.isSetFunctionFromTo fk.1 (low D (fk.1.input_mem_of_pairMember hDd)))
  have ext : Rf_ext_d I Y S := hq.extensional_l hZF hω mx.1 model (rf_ext_mem_l I hZF.1 hX mx)
  let d' : (smdl_structure_l I (R := S) model.2.1).Domain := ⟨d, fk.1.output_mem_of_pairMember hDd⟩
  let b' : (smdl_structure_l I (R := S) model.2.1).Domain := ⟨b, fk.1.output_mem_of_pairMember hAb⟩
  have codes := (rc_family_native_l I model.2.1 (ext.native_l I model.2.1) d' ft).mp functions
  obtain ⟨g, comp⟩ := cp0_exists_l (ZF.modelsKP hZF) (ff.mono_target_l (low A₀ (fk.1.input_mem_of_pairMember hAb)))
    (fn0_of_function_l (ZF.modelsKP hZF) fk.1)
  have hg := ((rr_bounded_functions_l hZF model.2.1 ext closed low algebra
    fk image pred d' b' hDd hAb ht codes g).mpr ⟨f, hf, ff, comp⟩).1
  obtain ⟨B₁, hB₁, gp⟩ := quotient.map.projection.2.2 g hg
  obtain ⟨u, pair⟩ := (I).total a B₁
  obtain ⟨E, _, huE⟩ := limit.projection.2.1 u ((system.nodes u).mpr ⟨a, B₁, pair, o, C₁, W₁, hao, quotient.code.1, hB₁⟩)
  exact ⟨g, E, comp, u, B₁, pair, quotient.map.representative_l I (family.at_l hZF.1 haU fa space).base gp, huE⟩

theorem Er_system_d.reindex_l {ω κ L Y S F k J O Z A p T V r C W m n a b t f E : M.Domain}
    (system : Er_system_d I ω κ L Y S F k J O Z A p T V) (limit : Di_limit_d A p T V r C W)
    (hm : M.mem m ω) (hn : M.mem n ω) (ft : Fn0_d m n t) (hb : M.mem b J)
    (fb : Fn0_d n L b) (fta : Cp0_d m n L t b a) (value : Ep_repr_d r a f E) :
    ∃ g, Ep_pull_d κ Y m n t f g ∧ Ep_repr_d r b g E := by
  obtain ⟨u, B, pu, hf, huE⟩ := value
  have hua := (system.index u a B pu).mpr (limit.projection.bound_l huE).1
  have ab := (system.order_spec a b).mpr ⟨(system.projection.bound_l hua).2, hb, t, m, n, hm, hn, ft, fb, fta⟩
  obtain ⟨v, hvb, huv⟩ := system.diagram.total u a b hua ab
  obtain ⟨P, pv, _⟩ := system.toEg_graph_d.label_l hvb
  obtain ⟨m', n', t', g, _, _, ft', fb', fta', hg, pull⟩ := system.representatives u v a b B P pu pv huv f hf
  have eq := fb'.domain_eq_l hZF.1 fb
  subst n'
  have eq := fta'.1.domain_eq_l hZF.1 fta.1
  subst m'
  obtain ⟨_, _, _, inj⟩ := (system.indices b).mp hb
  have eq := ec_factor_unique_l hZF.1 inj ft' ft fta' fta
  subst t'
  obtain ⟨E', _, hvE⟩ := limit.projection.2.1 v (system.projection.bound_l hvb).1
  exact ⟨g, pull, v, P, pv, hg, (limit.commute_l system.diagram huv huE hvE).symm ▸ hvE⟩

/-- 不同支撑的同一处处常值在原关系极限中有同一个值。 -/
theorem Er_system_d.constant_l {ω κ L N Y S F k J O Z A p T V r C W D E x a b f g H P : M.Domain}
    (family : Em_source_d ω κ L N F) (system : Er_system_d I ω κ L Y S F k J O Z A p T V)
    (limit : Di_limit_d A p T V r C W) (ff : Fn0_d D Y f) (fg : Fn0_d E Y g)
    (fc : Rs_const_d D x f) (gc : Rs_const_d E x g) (fv : Ep_repr_d r a f H) (gv : Ep_repr_d r b g P) : H = P := by
  obtain ⟨u, B, pu, hf, huH⟩ := fv
  obtain ⟨v, B', pv, hg, hvP⟩ := gv
  obtain ⟨c, w, z, hwc, hzc, huw, hvz⟩ := system.diagram.common_l (limit.projection.bound_l huH).1 (limit.projection.bound_l hvP).1
  obtain ⟨Q, pw, atQ⟩ := system.toEg_graph_d.label_l hwc
  obtain ⟨Q', pz, atQ'⟩ := system.toEg_graph_d.label_l hzc
  obtain ⟨o, C₀, W₀, hco, component, mc, hQC⟩ := system.model_l hZF atQ
  obtain ⟨_, hz⟩ := system.codes
  have hQ'C := (ep_at_read_l hz hco mc.1).mp atQ'
  obtain ⟨n, D₀, U, _, _, G, s, C₁, W₁, _, fn, space, hcU, _, _, _, quotient⟩ := component
  obtain ⟨rfl, rfl⟩ := smdl_unique_l I quotient.code mc
  have measure := (family.at_l hZF.1 hcU fn space).base
  have lift {D a B u f} (ff : Fn0_d D Y f) (fc : Rs_const_d D x f)
      (pu : KPair_d M u a B) (hf : M.mem f B) {Q w} (pw : KPair_d M w c Q) (huw : Rd_entry_d u w T) :
      ∃ g, M.mem g Q ∧ Rs_const_d D₀ x g := by
    obtain ⟨m, n', t, g, _, _, ft, fn', _, hg, pull⟩ := system.representatives u w a c B Q pu pw huw f hf
    have eq := fn'.domain_eq_l hZF.1 fn
    subst n'
    obtain ⟨D', ds, ff'⟩ := pull.1
    have eq := ff'.domain_eq_l hZF.1 ff
    subst D'
    refine ⟨g, hg, fun v hv => ?_⟩
    obtain ⟨t₀, comp⟩ := cp0_exists_l (ZF.modelsKP hZF) ft ((space v).mp hv)
    exact (pull.2.2 v t₀ ((space v).mp hv) comp x).mpr (fc t₀ ((ds t₀).mpr comp.1))
  obtain ⟨f', hf', fc'⟩ := lift ff fc pu hf pw huw
  obtain ⟨g', hg', gc'⟩ := lift fg gc pv hg pz hvz
  have sf := quotient.map.member_l I hZF.1 measure hQC hf'
  have sg := quotient.map.member_l I hZF.1 measure hQ'C hg'
  have fnf := quotient.map.functions f' (quotient.map.projection.input_mem_of_pairMember sf)
  have eq := (rp_kernel_l I hZF.1 measure quotient.map sf sg).mpr
    ⟨D₀, measure.top, fun s hs => ⟨x, (fnf.bound_l (fc' s hs)).2, fc' s hs, gc' s hs⟩⟩
  have wz := kpair_unique_l M hZF.1 pw (eq.symm ▸ pz)
  exact (limit.kernel u v H P huH hvP).mpr ⟨w, huw, wz.symm ▸ hvz⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 所属源有界关系与新极限关系的精确对应

两边使用同一个共同支撑和同一真实测度。值域只经已有低层实现搬运，
成员关系由完整前驱方程反映，不假设新极限良基。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal FilterZF
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem er_edge_iff_l {ω κ K L N Y S F Γ k J O Z A p T V r C W B U₀ R'
    m n a b D Q f g f' g' E H : M.Domain}
    (hω : M.IsOmega ω) (below : M.MemberSubset ω κ) (finite : Fseq_space_d I ω κ K)
    (family : Em_source_d ω κ L N F)
    (system : Er_system_d I ω κ L Y S F k J O Z A p T V) (limit : Di_limit_d A p T V r C W)
    (fk : M.IsSetInjectionFromTo I k Γ Y) (sub : M.MemberSubset B Γ)
    (pred : ∀ x z, Rd_entry_d x z k → ∀ w, Rd_entry_d w z S ↔ ∃ y, M.mem y x ∧ Rd_entry_d y w k)
    (membership : Rd_fun_d .mem B B B R') (measures : ∀ a U, Rd_entry_d a U F → M.mem U U₀)
    (hm : M.mem m ω) (hn : M.mem n ω) (fa : Fn0_d m L a) (fb : Fn0_d n L b)
    (space : Ep_space_d κ m D) (space' : Ep_space_d κ n Q) (ff : Fn0_d D B f) (gg : Fn0_d Q B g)
    (cf : Cp0_d D Γ Y f k f') (cg : Cp0_d Q Γ Y g k g')
    (fv : Ep_repr_d r a f' E) (gv : Ep_repr_d r b g' H) :
    Eb_edge_d ω κ L B J K U₀ R' F a f b g ↔ Rd_entry_d E H W := by
  have key := fn0_of_function_l (ZF.modelsKP hZF) fk.1
  have member x y x' y' (hx : M.mem x B) (hy : M.mem y B) (hxx : Rd_entry_d x x' k) (hyy : Rd_entry_d y y' k) :
      Rd_entry_d x y R' ↔ Rd_entry_d x' y' S :=
    (rt_mem_graph_l (ZF.modelsKP hZF) membership x y).trans
      ((and_iff_right hx).trans ((and_iff_right hy).trans
        ⟨fun h => (pred y y' hyy x').mpr ⟨x, h, hxx⟩, fun h => by
          obtain ⟨z, hz, hzx⟩ := (pred y y' hyy x').mp h
          exact fk.2 z x x' hzx hxx ▸ hz⟩))
  constructor
  · rintro ⟨c, hcJ, U, _, hcU, P, hPU, m', _, n', _, l, hl, s, _, t, _, fs, ft, fc, fsa, ftb, point⟩
    have eq := fsa.1.domain_eq_l hZF.1 fa
    subst m'
    have eq := ftb.1.domain_eq_l hZF.1 fb
    subst n'
    obtain ⟨f'', pf, fv'⟩ := system.reindex_l hZF limit hm hl fs hcJ fc fsa fv
    obtain ⟨g'', pg, gv'⟩ := system.reindex_l hZF limit hn hl ft hcJ fc ftb gv
    obtain ⟨D₁, functions⟩ := ZF.exists_functionSpace hZF I l κ
    have ds : Ep_space_d κ l D₁ := fun v => (functions v).trans
      ⟨fn0_of_function_l (ZF.modelsKP hZF), fn0_function_l (ZF.modelsKP hZF)⟩
    have measure := (family.at_l hZF.1 hcU fc ds).base
    apply (er_repr_atoms_l hZF family system limit hcU fv' gv').2.mpr
    refine ⟨P, hPU, fun v hv => ?_⟩
    obtain ⟨s₀, _, t₀, _, x, hx, y, hy, sv, tv, sx, ty, xy⟩ := point v hv
    obtain ⟨x', hx', hxx⟩ := fk.1.2.2 x (sub x hx)
    obtain ⟨y', hy', hyy⟩ := fk.1.2.2 y (sub y hy)
    have vf := (ds v).mp (measure.bounds P hPU v hv)
    exact ⟨x', hx', y', hy', (pf.2.2 v s₀ vf sv x').mpr ((cf.value_l (ff.mono_target_l sub) key sx).mpr hxx),
      (pg.2.2 v t₀ vf tv y').mpr ((cg.value_l (gg.mono_target_l sub) key ty).mpr hyy),
      (member x y x' y' hx hy hxx hyy).mp xy⟩
  · intro edge
    obtain ⟨u, P₀, pu, hfP, huE⟩ := fv
    obtain ⟨v, P₁, pv, hgP, hvH⟩ := gv
    obtain ⟨c, w, z, hwc, hzc, huw, hvz, hwz⟩ := (limit.relation u v E H huE hvH).mp edge
    obtain ⟨P, pw, atP⟩ := system.toEg_graph_d.label_l hwc
    obtain ⟨Q₁, pz, atQ⟩ := system.toEg_graph_d.label_l hzc
    obtain ⟨m', l, s, f'', _, hl, fs, fc, fsa, hfP', pf⟩ := system.representatives u w a c P₀ P pu pw huw f' hfP
    obtain ⟨n', l', t, g'', _, _, ft, fc', ftb, hgQ', pg⟩ := system.representatives v z b c P₁ Q₁ pv pz hvz g' hgP
    have eq := fsa.1.domain_eq_l hZF.1 fa
    subst m'
    have eq := ftb.1.domain_eq_l hZF.1 fb
    subst n'
    have eq := fc'.domain_eq_l hZF.1 fc
    subst l'
    obtain ⟨o, C₁, W₁, hco, component, model, hPC⟩ := system.model_l hZF atP
    obtain ⟨_, hz⟩ := system.codes
    have hQC := (ep_at_read_l hz hco model.1).mp atQ
    have relation := (ep_rel_read_l hz hco model.1).mp ((system.toEg_graph_d.relation_l pw pz).mp hwz).2.2
    obtain ⟨l', D₁, U, _, _, G, q₀, C₂, W₂, _, fc', ds, hcU, _, _, _, quotient⟩ := component
    obtain ⟨rfl, rfl⟩ := smdl_unique_l I quotient.code model
    have eq := fc'.domain_eq_l hZF.1 fc
    subst l'
    have measure := (family.at_l hZF.1 hcU fc ds).base
    obtain ⟨P', hPU, point⟩ := (quotient.relation f'' g'' P Q₁
      (quotient.map.member_l I hZF.1 measure hPC hfP') (quotient.map.member_l I hZF.1 measure hQC hgQ')).mp relation
    have sk := (finite s).mpr ⟨m, hm, fn0_function_l (ZF.modelsKP hZF)
      (fs.mono_target_l fun x hx => below x (hω.transitive (ZF.modelsKP hZF) l hl x hx))⟩
    have tk := (finite t).mpr ⟨n, hn, fn0_function_l (ZF.modelsKP hZF)
      (ft.mono_target_l fun x hx => below x (hω.transitive (ZF.modelsKP hZF) l hl x hx))⟩
    refine ⟨c, (system.projection.bound_l hwc).2, U, measures c U hcU, hcU, P', hPU,
      m, hm, n, hn, l, hl, s, sk, t, tk, fs, ft, fc, fsa, ftb, fun v hv => ?_⟩
    have vf := (ds v).mp (measure.bounds P' hPU v hv)
    obtain ⟨s₀, sv⟩ := cp0_exists_l (ZF.modelsKP hZF) fs vf
    obtain ⟨t₀, tv⟩ := cp0_exists_l (ZF.modelsKP hZF) ft vf
    obtain ⟨x, hx, sx⟩ := ff.2.1 s₀ ((space s₀).mpr sv.1)
    obtain ⟨y, hy, ty⟩ := gg.2.1 t₀ ((space' t₀).mpr tv.1)
    obtain ⟨x', _, y', _, vx, vy, xy⟩ := point v hv
    have hxx := (cf.value_l (ff.mono_target_l sub) key sx).mp ((pf.2.2 v s₀ vf sv x').mp vx)
    have hyy := (cg.value_l (gg.mono_target_l sub) key ty).mp ((pg.2.2 v t₀ vf tv y').mp vy)
    exact ⟨s₀, (finite s₀).mpr ⟨m, hm, fn0_function_l (ZF.modelsKP hZF) sv.1⟩,
      t₀, (finite t₀).mpr ⟨n, hn, fn0_function_l (ZF.modelsKP hZF) tv.1⟩,
      x, hx, y, hy, sv, tv, sx, ty, (member x y x' y' hx hy hxx hyy).mpr xy⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 下一共同低层的完整前驱实现

所属源的同一有界池直接投影到新原关系极限。精确关系与全部前驱覆盖
确定其传递值的唯一实现；整个新极限始终保持未坍塌。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal FilterZF
universe u
variable {M : Structure.{u}}

section Low
variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Eb_collapse_d.next_raw_l {ω c X R c' Y S q H N κ K L F R₀ Γ γ k J O Z A p T V r o C W j
    B₀ b D₀ a₀ f₀ H₀ D₁ Q₁ Γ₁ e : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (mx : Smem_d I c X R)
    (theory : Sc_theory_d I ω X R) (model : Smdl_d I c' Y S) (hq : Smap_d I ω c c' X Y q)
    (closed : Rr_closed_d I Y S H)
    (owner : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K N R₀) (hΓ : M.mem Γ N) (rank : Vr_d N γ Γ) (hγ : M.IsLimitOrdinal γ)
    (fk : M.IsSetInjectionFromTo I k Γ Y)
    (image : ∀ z, Rd_entry_d z H S ↔ ∃ x, M.mem x Γ ∧ Rd_entry_d x z k)
    (pred : ∀ x z, Rd_entry_d x z k → ∀ w, Rd_entry_d w z S ↔ ∃ y, M.mem y x ∧ Rd_entry_d y w k)
    (family : Em_source_d ω κ L N F) (system : Er_system_d I ω κ L Y S F k J O Z A p T V)
    (limit : Di_limit_d A p T V r C W) (next : Smdl_d I o C W) (embed : Smap_d I ω c' o Y C j)
    (hBb : Rd_entry_d B₀ b k) (trans : M.TransitiveSet B₀) (hbH : Rd_entry_d b H₀ j)
    (ff₀ : Fn0_d D₀ Y f₀) (constant : Rs_const_d D₀ b f₀) (fv : Ep_repr_d r a₀ f₀ H₀)
    (owned : Eb_collapse_d ω κ L K N B₀ F D₁ Q₁ Γ₁ e) :
    M.mem Γ₁ N ∧ ∃ k', M.IsSetInjectionFromTo I k' Γ₁ C ∧
      (∀ x E, Rd_entry_d x E k' ↔ ∃ u, M.mem u D₁ ∧ Rd_entry_d u x e ∧ Er_value_d κ Γ Y k r u E) ∧
      (∀ E, Rd_entry_d E H₀ W ↔ ∃ x, M.mem x Γ₁ ∧ Rd_entry_d x E k') ∧
      ∀ x E, Rd_entry_d x E k' → ∀ P, Rd_entry_d P E W ↔ ∃ y, M.mem y x ∧ Rd_entry_d y P k' := by
  obtain ⟨J₀, P₀, G₀, U₀, R₁, pool, indices, _, _, _, he, range, membership, _, edges, collapse, reflect⟩ := owned
  have eq := hZF.1.eq_of_same_members J₀ J (fun a => (indices a).trans (system.indices a).symm)
  subst J₀
  have low := rank.transitive_l owner.transitive hΓ
  have hB₀ := fk.1.input_mem_of_pairMember hBb
  have sub := low B₀ hB₀
  have algebra := (owner.algebra_l (ZF.modelsKP hZF)).rank_l hZF owner.transitive hΓ rank hγ
  have domain n a D (ha : M.mem a J) (fa : Fn0_d n L a) (ds : Ep_space_d κ n D) : M.mem D Γ := by
    obtain ⟨_, hz⟩ := system.codes
    obtain ⟨c, _, hac⟩ := hz.2.1 a ha
    obtain ⟨n', D', _, d, _, _, _, _, _, _, fa', ds', _, hDd, _, _, _⟩ := system.components a c hac
    have eq := fa'.domain_eq_l hZF.1 fa
    subst n'
    have eq := hZF.1.eq_of_same_members D' D (fun s => (ds' s).trans (ds s).symm)
    subst D'
    exact fk.1.input_mem_of_pairMember hDd
  have key := fn0_of_function_l (ZF.modelsKP hZF) fk.1
  -- 同一有界池的每个节点取得唯一原关系极限值，故可直接替换成实际求值图。
  let η : Env M 5 := ⟨Fin.cases r (Fin.cases k (Fin.cases Y (Fin.cases Γ (fun _ => κ)))), fun _ => κ⟩
  let φ : BinarySchema 5 := { body := er_value_m (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have sat u E : φ.denote η u E ↔ Er_value_d κ Γ Y k r u E := er_value_sat_l hZF.1 ..
  have total u (hu : M.mem u D₁) : ∃ E, φ.denote η u E := by
    obtain ⟨n, a, D, f, _, ha, fa, ds, hf, ff, pair⟩ := pool.read_l (ZF.modelsKP hZF) (owner.finite_l (ZF.modelsKP hZF)) hu
    have hfΓ := rank.relation_mem_l owner.transitive hΓ hγ (domain n a D ha fa ds) hB₀ hf ff.1
    obtain ⟨g, E, comp, value⟩ := system.bounded_value_l hZF hω hX mx model hq closed low algebra
      fk image pred family limit hBb ha fa ds hfΓ ff
    exact ⟨E, (sat u E).mpr ⟨a, f, n, D, g, pair, ds, ff.mono_target_l sub, comp, value⟩⟩
  have unique u (hu : M.mem u D₁) E H' (ev : φ.denote η u E) (hv : φ.denote η u H') : E = H' := by
    obtain ⟨a, f, n, D, g, pair, _, ff, comp, value⟩ := (sat u E).mp ev
    obtain ⟨a', f', _, D', g', pair', _, ff', comp', value'⟩ := (sat u H').mp hv
    obtain ⟨ea, ef⟩ := kpair_injective_l M pair' pair
    subst a' f'
    have eq := ff'.domain_eq_l hZF.1 ff
    subst D'
    have eq := cp0_unique_l hZF.1 ff key comp' comp
    subst g'
    obtain ⟨m, a₁, D₂, f₁, hm, _, fa, ds, _, ff₁, pair₁⟩ := pool.read_l (ZF.modelsKP hZF) (owner.finite_l (ZF.modelsKP hZF)) hu
    obtain ⟨ea, ef⟩ := kpair_injective_l M pair₁ pair
    subst a₁ f₁
    have eq := ff₁.domain_eq_l hZF.1 ff
    subst D₂
    obtain ⟨U, haU⟩ := family.total m a hm fa
    exact (er_repr_atoms_l hZF family system limit haU value value').1.mpr
      (rp_eq_refl_l (family.at_l hZF.1 haU fa ds).base comp.1)
  obtain ⟨v, vf, spec⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ η total unique (fun u E _ hv => by
    obtain ⟨_, _, _, _, _, _, _, _, _, w, _, _, _, hwE⟩ := (sat u E).mp hv
    exact (limit.projection.bound_l hwE).2)
  have values u E : Rd_entry_d u E v ↔ M.mem u D₁ ∧ Er_value_d κ Γ Y k r u E :=
    (spec u E).trans (and_congr_right fun _ => sat u E)
  have read u E (huE : Rd_entry_d u E v) : ∃ n a D f g,
      M.mem n ω ∧ M.mem a J ∧ Fn0_d n L a ∧ Ep_space_d κ n D ∧ M.mem f N ∧ Fn0_d D B₀ f ∧
        KPair_d M u a f ∧ Cp0_d D Γ Y f k g ∧ Ep_repr_d r a g E := by
    obtain ⟨hu, a', f', _, D', g, pair', _, ff', comp, ev⟩ := (values u E).mp huE
    obtain ⟨n, a, D, f, hn, ha, fa, ds, hf, ff, pair⟩ := pool.read_l (ZF.modelsKP hZF) (owner.finite_l (ZF.modelsKP hZF)) hu
    obtain ⟨ea, ef⟩ := kpair_injective_l M pair' pair
    subst a' f'
    have eq := ff'.domain_eq_l hZF.1 (ff.mono_target_l sub)
    subst D'
    exact ⟨n, a, D, f, g, hn, ha, fa, ds, hf, ff, pair, comp, ev⟩
  have relation u w E P (hu : Rd_entry_d u E v) (hw : Rd_entry_d w P v) : Rd_entry_d u w Q₁ ↔ Rd_entry_d E P W := by
    obtain ⟨m, a, D, f, f', hm, ha, fa, ds, _, ff, pu, cf, ev⟩ := read u E hu
    obtain ⟨n, b, Q, g, g', hn, hb, fb, qs, _, gg, pw, cg, pv⟩ := read w P hw
    have huD := vf.input_mem_of_pairMember hu
    have hwD := vf.input_mem_of_pairMember hw
    obtain ⟨a', _, f₁, hfG, pu', _⟩ := (pool.nodes u).mp huD
    obtain ⟨ea, ef⟩ := kpair_injective_l M pu' pu
    subst a' f₁
    obtain ⟨b', _, g₁, hgG, pw', _⟩ := (pool.nodes w).mp hwD
    obtain ⟨eb, eg⟩ := kpair_injective_l M pw' pw
    subst b' g₁
    have link : Eb_link_d ω κ L B₀ J K U₀ R₁ F G₀ u w ↔ Eb_edge_d ω κ L B₀ J K U₀ R₁ F a f b g := by
      refine ⟨?_, fun h => ⟨a, ha, f, hfG, b, hb, g, hgG, pu, pw, h⟩⟩
      rintro ⟨a', _, f₁, _, b', _, g₁, _, pu', pw', h⟩
      obtain ⟨ea, ef⟩ := kpair_injective_l M pu' pu
      subst a' f₁
      obtain ⟨eb, eg⟩ := kpair_injective_l M pw' pw
      subst b' g₁
      exact h
    exact (edges u w).trans ((and_iff_right huD).trans ((and_iff_right hwD).trans
      (link.trans (er_edge_iff_l hZF owner.omega owner.below (owner.finite_l (ZF.modelsKP hZF)) family system limit fk sub pred membership
        (fun a U h => (range U).mpr ⟨a, h⟩)
        hm hn fa fb ds qs ff gg cf cg ev pv))))
  -- 正反两向的有界代表定理给出全部成员覆盖，而非仅覆盖已选代表。
  have covers E : (∃ u, M.mem u D₁ ∧ Rd_entry_d u E v) ↔ Rd_entry_d E H₀ W := by
    constructor
    · rintro ⟨u, _, huE⟩
      obtain ⟨_, a, D, f, g, _, _, _, _, _, ff, _, comp, ev⟩ := read u E huE
      apply system.bound_mem_l hZF family limit (fk.1.output_mem_of_pairMember hBb) ff₀ constant fv (g := g) ?_ ev
      intro s y hsy
      obtain ⟨x, hx, hsx⟩ := ff.2.1 s (comp.1.bound_l hsy).1
      exact (pred B₀ b hBb y).mpr ⟨x, hx, (comp.value_l (ff.mono_target_l sub) key hsx).mp hsy⟩
    · intro edge
      obtain ⟨n, a, D, f, g, hn, ha, fa, ds, hf, ff, comp, ev⟩ := system.bounded_l hZF hω hX mx theory model hq closed
        low algebra fk image pred family limit hBb ff₀ constant fv edge
      obtain ⟨u, pair⟩ := (I).total a f
      have hu := pool.node_l (ZF.modelsKP hZF) (owner.finite_l (ZF.modelsKP hZF)) hn ha fa ds (owner.space_mem_l hZF hn ds) (owner.transitive Γ hΓ f hf) ff pair
      exact ⟨u, hu, (values u E).mpr ⟨hu, a, f, n, D, g, pair, ds, ff.mono_target_l sub, comp, ev⟩⟩
  have ext : Rf_ext_d I Y S := hq.extensional_l hZF hω mx.1 model (rf_ext_mem_l I hZF.1 hX mx)
  have nextExt := embed.extensional_l hZF hω model next ext
  let nx : Nonempty {x // M.mem x Γ} := ⟨⟨B₀, hB₀⟩⟩
  let ρ : Env (rt_model_l Γ nx) 1 := ⟨fun _ => ⟨B₀, hB₀⟩, fun _ => ⟨B₀, hB₀⟩⟩
  let η : Env (smdl_structure_l I (R := S) model.2.1) 1 :=
    ⟨fun _ => ⟨b, fk.1.output_mem_of_pairMember hBb⟩, fun _ => ⟨b, fk.1.output_mem_of_pairMember hBb⟩⟩
  let θ : Env (smdl_structure_l I (R := W) next.2.1) 1 :=
    ⟨fun _ => ⟨H₀, embed.1.1.output_mem_of_pairMember hbH⟩, fun _ => ⟨H₀, embed.1.1.output_mem_of_pairMember hbH⟩⟩
  have oldTrans := (rr_realize_delta_l I low nx model.2.1 fk pred (Formula.isTransitive .newest)
    (by simp -implicitDefEqProofs) (Formula.isTransitive_delta0 _) ρ η (fun _ => hBb)).mp
      ((Formula.satisfies_isTransitive_iff ..).mpr trans)
  have newTrans := (Formula.satisfies_isTransitive_iff ..).mp
    ((smap_source_l I hZF hω model next embed (Formula.isTransitive .newest) (by simp -implicitDefEqProofs)
      η θ (fun _ => hbH)).mp oldTrans)
  -- H₀ 的传递性将完整成员覆盖提升为每个像点的完整前驱覆盖。
  have leftExt x (hx : M.mem x Γ₁) y (hy : M.mem y Γ₁)
      (same : ∀ z, M.mem z Γ₁ → (M.mem z x ↔ M.mem z y)) : x = y :=
    hZF.1.eq_of_same_members x y (fun z => ⟨fun hz => (same z (collapse.transitive x hx z hz)).mp hz,
      fun hz => (same z (collapse.transitive y hy z hz)).mpr hz⟩)
  obtain ⟨k', fk', graph, _, predecessor⟩ := rr_span_realize_l hZF M.mem collapse.function collapse.onto leftExt reflect
    (fun u x hux y hy => collapse.onto y (collapse.transitive x (collapse.function.bound_l hux).2 y hy))
    (fn0_of_function_l (ZF.modelsKP hZF) vf)
    nextExt relation (fun u E huE P hPE => (covers P).mpr
      (newTrans ⟨E, vf.output_mem_of_pairMember huE⟩ ((covers E).mp ⟨u, vf.input_mem_of_pairMember huE, huE⟩)
        ⟨P, (limit.bounded P E hPE).1⟩ hPE))
  obtain ⟨c₀, mc₀⟩ := owner.code
  obtain ⟨Γ', hΓ', rg⟩ := sc_range_source_l hZF owner.omega owner.transitive mc₀ owner.theory he
  have eq := hZF.1.eq_of_same_members Γ' Γ₁ (fun x => (rg x).trans
    ⟨fun ⟨u, hux⟩ => (collapse.function.bound_l hux).2, fun hx => (collapse.onto x hx).imp fun _ h => h.2⟩)
  refine ⟨eq ▸ hΓ', k', fk', fun x E => (graph x E).trans ?_, fun E => ?_, predecessor⟩
  · exact exists_congr fun u => and_congr_right fun hu => and_congr_right fun _ =>
      (values u E).trans (and_iff_right hu)
  · refine (covers E).symm.trans ⟨?_, ?_⟩
    · rintro ⟨u, hu, huE⟩
      obtain ⟨x, hx, hux⟩ := collapse.function.2.1 u hu
      exact ⟨x, hx, (graph x E).mpr ⟨u, hu, hux, huE⟩⟩
    · rintro ⟨x, _, hxE⟩
      obtain ⟨u, hu, _, huE⟩ := (graph x E).mp hxE
      exact ⟨u, hu, huE⟩

end Low

section Successor
variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 同时构造完整原关系后继及下一共同低层；所有分量与实现图均由上述构造产生。 -/
theorem er_successor_l {ω c X R c' Y S q H N κ K L F R₀ Γ γ k B₀ D Q Γ₁ e : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (mx : Smem_d I c X R)
    (theory : Sc_theory_d I ω X R)
    (collection : Sc_collection_d I ω X R)
    (model : Smdl_d I c' Y S)
    (hq : Smap_d I ω c c' X Y q)
    (small : Rr_small_d I Y S H)
    (closed : Rr_closed_d I Y S H)
    (owner : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K N R₀) (hΓ : M.mem Γ N) (rank : Vr_d N γ Γ)
    (hγ : M.IsLimitOrdinal γ) (hκ : M.mem κ Γ)
    (fk : M.IsSetInjectionFromTo I k Γ Y)
    (image : ∀ z, Rd_entry_d z H S ↔ ∃ x, M.mem x Γ ∧ Rd_entry_d x z k)
    (pred : ∀ x z, Rd_entry_d x z k → ∀ w, Rd_entry_d w z S ↔ ∃ y, M.mem y x ∧ Rd_entry_d y w k)
    (family : Em_source_d ω κ L N F)
    (coherent : Ec_source_d I ω κ L N F)
    (hB₀ : M.mem B₀ Γ) (trans₀ : M.TransitiveSet B₀)
    (owned : Eb_collapse_d ω κ L K N B₀ F D Q Γ₁ e) :
    ∃ J O Z A p T V r o C W j q' k' H', Er_system_d I ω κ L Y S F k J O Z A p T V ∧
      Di_limit_d A p T V r C W ∧ Smdl_d I o C W ∧ Di_elementary_d I ω O A p T V ∧
      Smap_d I ω c' o Y C j ∧ Smap_d I ω c o X C q' ∧
      (Zc_model_d I ω c X R → Zc_model_d I ω o C W) ∧
      (∀ x z, Rd_entry_d x z q' ↔ M.mem x X ∧ ∃ y, Rd_entry_d x y q ∧ Rd_entry_d y z j) ∧
      M.mem Γ₁ N ∧ Rr_layer_d I Γ₁ C W H' k' ∧
      (∀ x E, Rd_entry_d x E k' ↔ ∃ u, M.mem u D ∧ Rd_entry_d u x e ∧ Er_value_d κ Γ Y k r u E) ∧
      (∀ x E, Rd_entry_d x E j → ∃ a D f, Fn0_d D Y f ∧ Rs_const_d D x f ∧ Ep_repr_d r a f E) ∧
      ∃ b, Rd_entry_d B₀ b k ∧ Rd_entry_d b H' j := by
  have fs := owner.rank_read_source_l hZF hΓ rank hγ
    (rank.subset_mem_l owner.transitive hΓ hκ owner.omega_mem owner.below)
  obtain ⟨cΓ, RΓ, mg⟩ := smdl_membership_l I hZF ⟨κ, hκ⟩
  have tg := owner.rank_theory_l hZF hΓ rank hγ mg
  obtain ⟨J, O, Z, A, p, T, V, r, o, C, W, j, q', system, limit, next, elem, embed, root, certificate, comp, a₀, D₀, _, _, constants⟩ :=
    er_ultrapower_l hZFC hω hX mx theory collection model hq small closed fs mg tg (owner.transitive Γ hΓ)
      hκ fk image pred family coherent
  obtain ⟨b, hb, hBb⟩ := fk.1.2.2 B₀ hB₀
  obtain ⟨H', _, hbH⟩ := embed.1.1.2.2 b hb
  obtain ⟨P, f, u, ff, hf, fc, pair, huH⟩ := constants b H' hbH
  obtain ⟨hΓ₁, k', fk', graph, covers, predecessor⟩ := owned.next_raw_l hZF hω hX mx theory model hq closed owner hΓ rank hγ
    fk image pred family system limit next embed hBb trans₀ hbH ff fc ⟨u, P, pair, hf, huH⟩
  have transitive : M.TransitiveSet Γ₁ := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, collapse, _⟩ := owned
    exact collapse.transitive
  refine ⟨J, O, Z, A, p, T, V, r, o, C, W, j, q', k', H', system, limit, next, elem, embed, root, certificate, comp,
    hΓ₁, ⟨transitive, embed.1.1.output_mem_of_pairMember hbH, fk', covers, predecessor⟩,
    graph, ?_, b, hBb, hbH⟩
  intro x E hxE
  obtain ⟨P, f, u, ff, hf, fc, pair, huE⟩ := constants x E hxE
  exact ⟨a₀, D₀, f, ff, fc, u, P, pair, hf, huE⟩

end Successor
end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 新共同层的相对秩与递归闭包

新层只用所属侧的有界坍塌；相对秩直接沿原关系常值嵌入传输。
低层之间的实际图由完整前驱实现构造，并逐点交换。整个后继无需
所属模型的整体传递超幂，也不要求原关系极限预先良基。对于含 ω 的
极限共同层，还输出下一层的全部内部有限读写闭包及同一 ω 的固定性。
全内部分离由原关系分离和完整前驱回收构造；相对幂集从原层的实际
幂集证书传输。新层模型码、源理论和相对幂集均作为后继结果返回。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem er_rank_successor_l {ω c X R c' Y S q H N κ K L F R₀ Γ γ k B D Q Γ' e α : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (mx : Smem_d I c X R)
    (theory : Sc_theory_d I ω X R) (collection : Sc_collection_d I ω X R)
    (model : Smdl_d I c' Y S) (hq : Smap_d I ω c c' X Y q)
    (small : Rr_small_d I Y S H) (closed : Rr_closed_d I Y S H)
    (owner : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K N R₀) (hΓ : M.mem Γ N) (rank : Vr_d N γ Γ)
    (hγ : M.IsLimitOrdinal γ) (hκ : M.mem κ Γ) (fk : M.IsSetInjectionFromTo I k Γ Y)
    (image : ∀ z, Rd_entry_d z H S ↔ ∃ x, M.mem x Γ ∧ Rd_entry_d x z k)
    (pred : ∀ x z, Rd_entry_d x z k → ∀ w, Rd_entry_d w z S ↔ ∃ y, M.mem y x ∧ Rd_entry_d y w k)
    (family : Em_source_d ω κ L N F) (coherent : Ec_source_d I ω κ L N F)
    (hB : M.mem B Γ) (hα : M.mem α Γ) (rankB : Vr_d N α B)
    (height : M.IsLimitOrdinal α) (omega : M.mem ω B) (power : Sc_power_d B)
    (owned : Eb_collapse_d ω κ L K N B F D Q Γ' e) :
    ∃ J O Z A p T V r o C W j q' k' H' σ a₁ R₁, Er_system_d I ω κ L Y S F k J O Z A p T V ∧
      Di_limit_d A p T V r C W ∧ Smdl_d I o C W ∧ Di_elementary_d I ω O A p T V ∧
      Smap_d I ω c' o Y C j ∧ Smap_d I ω c o X C q' ∧
      (Zc_model_d I ω c X R → Zc_model_d I ω o C W) ∧
      (∀ x z, Rd_entry_d x z q' ↔ M.mem x X ∧ ∃ y, Rd_entry_d x y q ∧ Rd_entry_d y z j) ∧
      Rr_layer_d I Γ' C W H' k' ∧ M.IsSetInjectionFromTo I σ B Γ' ∧
      (∀ x E, Rd_entry_d x E k' ↔ ∃ u, M.mem u D ∧ Rd_entry_d u x e ∧ Er_value_d κ Γ Y k r u E) ∧
      (∀ x y z, Rd_entry_d x y σ → Rd_entry_d x z k → ∀ w,
        Rd_entry_d z w j ↔ Rd_entry_d y w k') ∧
      Fs_read_d ω Γ' ∧ (∀ a, M.mem a Γ' → ∃ p, M.mem p Γ' ∧ M.IsUnionOf p a) ∧
      Rd_entry_d ω ω σ ∧
      Smem_d I a₁ Γ' R₁ ∧ Sc_theory_d I ω Γ' R₁ ∧ Sc_power_d Γ' ∧
      Rr_closed_d I C W H' ∧ Rr_small_d I C W H' ∧
      ∃ a a', Rd_entry_d α a k ∧ Rd_entry_d a a' j ∧ Rr_rank_d I C W a' H' := by
  have hBN := owner.transitive Γ hΓ B hB
  have trans := rankB.transitive_l owner.transitive hBN
  obtain ⟨J, O, Z, A, p, T, V, r, o, C, W, j, q', k', H', system, limit, next, elem,
    embed, root, certificate, comp, _, layer, graph, _, b, hBb, hbH⟩ :=
    er_successor_l hZFC hω hX mx theory collection model hq small closed owner hΓ rank hγ hκ fk image pred
      family coherent hB trans owned
  have low := rank.transitive_l owner.transitive hΓ
  obtain ⟨v, hv, hκv⟩ := fk.1.2.2 κ hκ
  have hH : M.mem H Y := (model.2.2.2 v H ((image v).mpr ⟨κ, hκ, hκv⟩)).2
  let current : Rr_layer_d I Γ Y S H k := ⟨low, hH, fk, image, pred⟩
  obtain ⟨t, left, restrict⟩ := current.restrict_l I hZF trans hBb
  -- 在两个已实现低层之间构造真实函数图，不借用整体坍塌后的嵌入。
  obtain ⟨σ, fn, values⟩ := embed.layer_map_l hZF hω model next left layer hbH
  have square x y z (hxy : Rd_entry_d x y σ) (hxz : Rd_entry_d x z k) w :
      Rd_entry_d z w j ↔ Rd_entry_d y w k' := by
    obtain ⟨_, a, b, ha, hab, hyb⟩ := (values x y).mp hxy
    have ea := fk.1.1.2 x a z ((restrict.2 x a).mp ha).2 hxz
    subst a
    exact ⟨fun hzw => (embed.1.1.1.2 z b w hab hzw) ▸ hyb,
      fun hyw => (layer.injection.1.1.2 y b w hyb hyw) ▸ hab⟩
  -- 下一层的全部内部有限图及其空间由原关系边传递，不重建传递高模型。
  have read := owner.rank_read_source_l hZF hBN rankB height omega
  have unions a (ha : M.mem a B) : ∃ p, M.mem p B ∧ M.IsUnionOf p a := by
    obtain ⟨p, hp, code⟩ := (owner.algebra_l (ZF.modelsKP hZF)).union a (owner.transitive B hBN a ha)
    exact ⟨p, rankB.union_mem_l owner.transitive hBN ha hp code, code⟩
  obtain ⟨read', unions', omega'⟩ := read.map_layer_l hZF hω unions model next embed left layer hbH
  have fixedω := (values ω ω).mpr ⟨omega, omega'⟩
  have cut := (rank.rank_l hZF owner.transitive hΓ hγ hα hBN rankB).2
  obtain ⟨closedB, smallB⟩ := rr_rank_low_l hZF low fk image pred closed small hB cut hBb
  have closed' := (embed.rr_closed_l I hZF hω model next hbH).mp closedB
  have small' := (embed.rr_small_l I hZF hω model next hbH).mp smallB
  -- 有限代数与相对幂集的全称句子覆盖新层的全部新参数。
  let nb : Nonempty {x // M.mem x B} := ⟨⟨ω, omega⟩⟩
  let ng : Nonempty {x // M.mem x Γ'} := ⟨⟨ω, read'.omega_mem⟩⟩
  let ε : Env (rt_model_l B nb) 0 := ⟨Fin.elim0, fun _ => ⟨ω, omega⟩⟩
  have algebra := (owner.algebra_l (ZF.modelsKP hZF)).rank_l hZF owner.transitive hBN rankB height
  have valid : Formula.satisfies ε (.conj sc_algebra_m sc_power_m) :=
    ⟨(sc_algebra_sat_l (ZF.modelsKP hZF) trans nb ε).mpr algebra, (sc_power_sat_l trans nb ε).mpr power⟩
  obtain ⟨θ, _, truth⟩ := embed.relative_image_l hZF hω model next left layer nb ng hbH
    (.conj sc_algebra_m sc_power_m) (by simp -implicitDefEqProofs [sc_algebra_m, Definitional.Formula.FreeClosed]) ε
  obtain ⟨algebra', power'⟩ := truth.mp valid
  have algebra' := (sc_algebra_sat_l (ZF.modelsKP hZF) layer.transitive ng θ).mp algebra'
  have power' := (sc_power_sat_l layer.transitive ng θ).mp power'
  obtain ⟨a₁, R₁, lowModel⟩ := smdl_membership_l I hZF ⟨ω, read'.omega_mem⟩
  have atoms a b x y (ha : Rd_entry_d a x k') (hb : Rd_entry_d b y k') :
      Rd_entry_d a b R₁ ↔ Rd_entry_d x y W := by
    apply (lowModel.2 a b).trans
    exact ⟨fun h => (layer.predecessors b y hb x).mpr ⟨a, h.2.2, ha⟩, fun h => by
      obtain ⟨z, hz, hzx⟩ := (layer.predecessors b y hb x).mp h
      exact ⟨layer.injection.1.input_mem_of_pairMember ha, layer.injection.1.input_mem_of_pairMember hb,
        layer.injection.2 z a x hzx ha ▸ hz⟩⟩
  have theory' : Sc_theory_d I ω Γ' R₁ :=
    ⟨fun _ _ _ _ _ _ _ => rr_separation_l hZF hω mx.1 theory next root layer.member
      layer.injection layer.image atoms closed',
      (sc_algebra_mem_l I (ZF.modelsKP hZF) lowModel layer.transitive).mpr algebra'⟩
  -- 同一秩历史先由完整前驱图解释，再沿实际常值嵌入进入新极限。
  obtain ⟨a, ha, hαa⟩ := fk.1.2.2 α hα
  obtain ⟨a', ha', haa⟩ := embed.1.1.2.2 a ha
  have ext : Rf_ext_d I Y S := hq.extensional_l hZF hω mx.1 model (rf_ext_mem_l I hZF.1 hX mx)
  have oldRank := rr_realize_rank_l hZF model ext low fk image pred closed
    ⟨a, ha⟩ ⟨b, fk.1.output_mem_of_pairMember hBb⟩ hαa hBb cut
  let ρ : Env (smdl_structure_l I (R := S) model.2.1) 2 :=
    ⟨Fin.cases ⟨b, fk.1.output_mem_of_pairMember hBb⟩ (fun _ => ⟨a, ha⟩), fun _ => ⟨a, ha⟩⟩
  let η : Env (smdl_structure_l I (R := W) next.2.1) 2 :=
    ⟨Fin.cases ⟨H', embed.1.1.output_mem_of_pairMember hbH⟩ (fun _ => ⟨a', ha'⟩), fun _ => ⟨a', ha'⟩⟩
  have moved := (smap_source_l I hZF hω model next embed (v_sigma_m (.bound 1) .newest)
    (by simp -implicitDefEqProofs) ρ η (Fin.cases hbH (fun _ => haa))).mp oldRank
  exact ⟨J, O, Z, A, p, T, V, r, o, C, W, j, q', k', H', σ, a₁, R₁, system, limit, next, elem, embed, root, certificate, comp,
    layer, fn, graph, square, read', unions', fixedω, lowModel, theory', power',
    closed', small', a, a', hαa, haa, ha', layer.member, moved⟩

end YesMetaZFC.SetTheory.LargeCardinal
