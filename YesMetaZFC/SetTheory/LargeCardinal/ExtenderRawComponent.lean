import YesMetaZFC.SetTheory.LargeCardinal.ExtenderRawProjection
import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.RelationFamily

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

theorem er_component_exists_l {ω c X R c' Y S q B H Γ k N κ L F a n D U : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (mx : Smem_d Kp c X R)
    (theory : Sc_theory_d Kp ω X R) (collection : Sc_collection_d Kp ω X R)
    (model : Smdl_d Kp c' Y S) (hq : Smap_d Kp ω c c' X Y q) (hBH : Rd_entry_d B H q)
    (trans : M.TransitiveSet B) (small : Sc_small_d X B)
    (closed : ∀ a b, M.mem a B → M.mem b X → M.MemberSubset b a → M.mem b B)
    (hΓ : M.TransitiveSet Γ) (inside : M.MemberSubset Γ N) (fk : M.IsSetInjectionFromTo Kp k Γ Y)
    (image : ∀ z, Rd_entry_d z H S ↔ ∃ x, M.mem x Γ ∧ Rd_entry_d x z k)
    (pred : ∀ x z, Rd_entry_d x z k → ∀ w, Rd_entry_d w z S ↔ ∃ y, M.mem y x ∧ Rd_entry_d y w k)
    (hn : M.mem n ω) (fa : Fn0_d n L a) (space : Ep_space_d κ n D) (haU : Rd_entry_d a U F)
    (hD : M.mem D Γ) (measure : Sf_ultra_d N D U) : ∃ o, Er_component_d Kp ω κ L Y S F k a o := by
  obtain ⟨d, t, P, V, hDd, hdH, ht, ft, domain, hP, inN, ultra, restrict⟩ :=
    hq.measure_raw_l Kp hZF hω hX mx theory model hBH closed hΓ inside fk image pred hD measure
  have hd := fk.1.output_mem_of_pairMember hDd
  obtain ⟨μ, e, index⟩ := hq.small_raw_l hZF hω hX mx model hBH trans small ⟨d, hd⟩ hdH
  obtain ⟨G, o, p, C, T, _, _, quotient, _, functions, _⟩ := rc_successor_l hZF hω hX mx theory collection model hq
    ⟨d, hd⟩ μ e index (fn0_of_function_l (ZF.modelsKP hZF) ft) domain hP inN measure ultra restrict
  have ext : Rf_ext_d Kp Y S := hq.extensional_l hZF hω mx.1 model (rf_ext_mem_l Kp hZF.1 hX mx)
  exact ⟨o, n, D, U, d, t, G, p, C, T, hn, fa, space, haU, hDd, ht,
    (rc_family_native_l Kp model.2.1 (ext.native_l Kp model.2.1) ⟨d, hd⟩ (fn0_of_function_l (ZF.modelsKP hZF) ft)).mpr functions, quotient⟩

end Construction
end YesMetaZFC.SetTheory.LargeCardinal
