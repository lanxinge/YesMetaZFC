import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawGraphSyntax
import YesMetaZFC.Model.SetTheory.ReducedPower.RelationCopyPull
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawCopyClass
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.ActivityRead
import YesMetaZFC.SetTheory.Card.FiniteSequenceCountable
import YesMetaZFC.SetTheory.Card.OrdinalImage

/-! # 原关系超幂代表的有限对象码

以支撑、所属侧有限幂码、测度码和前驱侧函数码编号实际极限像。
后三项均是原载体中的对象；坐标展开、商投影和标签仍取实际集合图。
固定这些原对象后，其极限像唯一，无须选取商类代表。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def Er_count_repr_d (N T Y S k r v E : M.Domain) : Prop :=
  ∃ a d u f b e o D i t y V G p C W g B s,
    KPair_d M v a b ∧ KPair_d M b d e ∧ KPair_d M e u f ∧
    (∀ x, M.mem x D ↔ M.mem x N ∧ Rd_entry_d x d T) ∧
    Fn0_d D N i ∧ (∀ x z, Rd_entry_d x z i ↔ M.mem x D ∧ x = z) ∧
    M.IsRestrictionOf I t k D ∧ Fn0_d D Y t ∧ Rd_entry_d d y k ∧
    (∀ A, M.mem A V ↔ ∃ B, M.mem B N ∧ Rd_entry_d B u T ∧ Rt_trace_d I D i T B A) ∧
    Rc_family_d I Y S D y t G ∧ Rp_model_d I D Y V S o G p C W ∧
    M.mem g G ∧ Rf_fun_d I Y S y f ∧ Rc_graph_d I Y S t f g ∧
    Rd_entry_d g B p ∧ KPair_d M s a B ∧ Rd_entry_d s E r

def er_count_repr_m {n} (N T Y S k r v E : Term n) : Formula 1 n := set[n] ⟪
  ∃ a d u f b e o D i t y V G p C W g B s,
    ⌜kpair0_m⌝ₚ(⌜v⌝ₛ, a, b) ∧ ⌜kpair0_m⌝ₚ(b, d, e) ∧ ⌜kpair0_m⌝ₚ(e, u, f) ∧
    (∀ x, x ∈ D ↔ x ∈ ⌜N⌝ₛ ∧ ⌜rd_entry0_m⌝ₚ(x, d, ⌜T⌝ₛ)) ∧
    ⌜fn0_m⌝ₚ(D, ⌜N⌝ₛ, i) ∧ (∀ x z, ⌜rd_entry0_m⌝ₚ(x, z, i) ↔ x ∈ D ∧ x = z) ∧
    ⌜Formula.isRestriction kpair_convention_l⌝ₚ(t, ⌜k⌝ₛ, D) ∧ ⌜fn0_m⌝ₚ(D, ⌜Y⌝ₛ, t) ∧ ⌜rd_entry0_m⌝ₚ(d, y, ⌜k⌝ₛ) ∧
    (∀ A, A ∈ V ↔ (∃ B ∈ ⌜N⌝ₛ, ⌜rd_entry0_m⌝ₚ(B, u, ⌜T⌝ₛ) ∧
      ⌜rt_trace_m (𝒞 := kpair_convention_l)⌝ₚ(D, i, ⌜T⌝ₛ, B, A))) ∧
    ⌜rc_family_m⌝ₚ(⌜Y⌝ₛ, ⌜S⌝ₛ, D, y, t, G) ∧
    ⌜rp_model_m (𝒞 := kpair_convention_l)⌝ₚ(D, ⌜Y⌝ₛ, V, ⌜S⌝ₛ, o, G, p, C, W) ∧
    g ∈ G ∧ ⌜rf_fun_m (𝒞 := kpair_convention_l)⌝ₚ(⌜Y⌝ₛ, ⌜S⌝ₛ, y, f) ∧
    ⌜rc_graph_m (𝒞 := kpair_convention_l)⌝ₚ(⌜Y⌝ₛ, ⌜S⌝ₛ, t, f, g) ∧ ⌜rd_entry0_m⌝ₚ(g, B, p) ∧
    ⌜kpair0_m⌝ₚ(s, a, B) ∧ ⌜rd_entry0_m⌝ₚ(s, ⌜E⌝ₛ, ⌜r⌝ₛ)⟫
derive_free_closed er_count_repr_m

theorem er_count_repr_sat_l (ext : Extensional M) {n} (ρ : Env M n) (N T Y S k r v E : Term n) :
    Formula.satisfies ρ (er_count_repr_m N T Y S k r v E) ↔
      Er_count_repr_d I (N.eval ρ) (T.eval ρ) (Y.eval ρ) (S.eval ρ) (k.eval ρ) (r.eval ρ) (v.eval ρ) (E.eval ρ) := by
  simp only [er_count_repr_m, Er_count_repr_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    kpair0_sat_l ext, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff,
    rd_entry0_sat_l ext, fn0_sat_l ext, Formula.satisfies_extensionalEq_iff_eq ext,
    Formula.satisfies_isRestriction_iff I, Formula.satisfies_existsMem_iff, rt_trace_sat_l I,
    rc_family_sat_l I ext, rp_model_sat_l I ext, rf_fun_sat_l I, rc_graph_sat_l I ext, Definitional.Term.eval_weaken]
  rfl

section Unique
variable (ext : Extensional M)
include ext

theorem Er_count_repr_d.unique_l {N T Y S k r v E E' A H : M.Domain}
    (fk : M.IsSetFunction I k) (fr : Fn0_d A H r)
    (h : Er_count_repr_d I N T Y S k r v E) (h' : Er_count_repr_d I N T Y S k r v E') : E = E' := by
  have entry {x y q} (h : Rd_entry_d x y q) : M.PairMember I x y q := by
    obtain ⟨p, pair, hp⟩ := h
    let ρ : Env M 3 := ⟨Fin.cases p (Fin.cases x (fun _ => y)), fun _ => p⟩
    exact ⟨p, (I.satisfies_code_iff ρ .newest (.bound 1) (.bound 2)).mp
      ((kpair_sat_l M ext ρ .newest (.bound 1) (.bound 2)).mpr pair), hp⟩
  obtain ⟨a, d, u, f, b, e, o, D, i, t, y, V, G, p, C, W, g, B, s,
    va, bd, eu, dc, fi, id, rt, ft, kdy, measure, family, model, hg, _, graph, gp, sa, sr⟩ := h
  obtain ⟨a', d', u', f', b', e', o', D', i', t', y', V', G', p', C', W', g', B', s',
    va', bd', eu', dc', fi', id', rt', _, kdy', measure', family', model', hg', _, graph', gp', sa', sr'⟩ := h'
  obtain ⟨ea, eb⟩ := kpair_injective_l M va' va
  subst a' b'
  obtain ⟨ed, ee⟩ := kpair_injective_l M bd' bd
  subst d' e'
  obtain ⟨eu, ef⟩ := kpair_injective_l M eu' eu
  subst u' f'
  have eq := ext.eq_of_same_members D' D (fun x => (dc' x).trans (dc x).symm)
  subst D'
  have eq := fi'.ext_l ext fi (fun x hx =>
    ⟨x, (id' x x).mpr ⟨hx, rfl⟩, (id x x).mpr ⟨hx, rfl⟩⟩)
  subst i'
  have eq := rt'.1.eq_of_pairMember_iff ext rt.1 (fun x z => (rt'.2 x z).trans (rt.2 x z).symm)
  subst t'
  have eq := fk.2 d y' y (entry kdy') (entry kdy)
  subst y'
  have eq := ext.eq_of_same_members V' V (fun B => (measure' B).trans (measure B).symm)
  subst V'
  have eq := ext.eq_of_same_members G' G (fun g => (family' g).trans (family g).symm)
  subst G'
  have eq := model'.map.projection.1.1.eq_of_pairMember_iff ext model.map.projection.1.1
    (fun g B => (model'.map.classes g B).trans (model.map.classes g B).symm)
  subst p'
  have eq := graph'.unique_l I ext ft ((family g').mp hg').1 ((family g).mp hg).1 graph
  subst g'
  have eq := model.map.projection.1.2 g B' B (entry gp') (entry gp)
  subst B'
  have sr' : Rd_entry_d s E' r := kpair_unique_l M ext sa' sa ▸ sr'
  exact fr.2.2 s (fr.bound_l sr).1 E (fr.bound_l sr).2 E' (fr.bound_l sr').2 sr sr'

end Unique
end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 可数原关系模型的实际扩展器极限仍可数

全部支撑及三个原对象组成可数乘积。分离出合法代表码后，唯一像关系
形成一个满射到原直接极限的集合函数；取最小自然数编号给出计数界。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem er_countable_l {ω L N T κ ℓ F z Γ Y S k J O Z A p V W r H R : M.Domain}
    (hω : M.IsOmega ω) (cn : M.CardinalLessOrEqual I N ω) (cy : M.CardinalLessOrEqual I Y ω)
    (cl : M.CardinalLessOrEqual I L ω) (fk : M.IsSetFunctionFromTo I k Γ Y)
    (down : ∀ d x, M.mem d Γ → M.mem x N → Rd_entry_d x d T → M.mem x Γ)
    (h : Er_graph_d I ω L N T κ ℓ F z Y S k J O Z A p V W)
    (limit : Di_limit_d A p V W r H R) : M.CardinalLessOrEqual I H ω := by
  have small {B D} (sub : M.MemberSubset B D) (cd : M.CardinalLessOrEqual I D ω) :
      M.CardinalLessOrEqual I B ω := by
    obtain ⟨f, hf⟩ := ZF.exists_inclusionInjection hZF I sub
    obtain ⟨g, hg⟩ := cd
    exact ZF.exists_compositionInjection hZF I hf hg
  obtain ⟨P, ps, cp⟩ := ZF.fseq_countable_space_l I hZF hω cl
  have cj : M.CardinalLessOrEqual I J ω := small (fun a ha => by
    obtain ⟨n, hn, fa, _⟩ := (h.indices a).mp ha
    exact (ps a).mpr ⟨n, hn, fn0_function_l (ZF.modelsKP hZF) fa⟩) cp
  obtain ⟨H₂, prod₂⟩ := ZF.exists_cartesianProduct hZF I N Y
  obtain ⟨H₁, prod₁⟩ := ZF.exists_cartesianProduct hZF I N H₂
  obtain ⟨H₀, prod₀⟩ := ZF.exists_cartesianProduct hZF I J H₁
  have ch := ZF.countable_product_l I hZF hω cj
    (ZF.countable_product_l I hZF hω cn (ZF.countable_product_l I hZF hω cn cy prod₂) prod₁) prod₀
  let ρ : Env M 6 := ⟨Fin.cases r (Fin.cases k (Fin.cases S (Fin.cases Y (Fin.cases T (fun _ => N))))), fun _ => N⟩
  let φ : BinarySchema 6 := {
    body := er_count_repr_m (.bound 7) (.bound 6) (.bound 5) (.bound 4)
      (.bound 3) (.bound 2) (.bound 1) .newest }
  have sat v E : φ.denote ρ v E ↔ Er_count_repr_d I N T Y S k r v E := er_count_repr_sat_l I hZF.1 ..
  let ψ : UnarySchema 6 := { body := .existsE φ.body, freeClosed := φ.freeClosed }
  obtain ⟨B, bs⟩ := ZF.separation_exists_d hZF ψ ρ H₀
  have legal v : M.mem v B ↔ M.mem v H₀ ∧ ∃ E, φ.denote ρ v E := by
    simpa only [ψ, UnarySchema.denote, Formula.satisfies_exists_iff] using! bs v
  have bound {v E} (he : Er_count_repr_d I N T Y S k r v E) : M.mem E H := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, image⟩ := he
    exact (limit.projection.bound_l image).2
  obtain ⟨f, ff, fs⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := B) (target := H)
    (fun v hv => ((legal v).mp hv).2)
    (fun v _ E E' he he' => ((sat v E).mp he).unique_l I hZF.1 fk.1 limit.projection ((sat v E').mp he'))
    (fun _ _ _ he => bound ((sat _ _).mp he))
  have onto E (he : M.mem E H) : ∃ v, M.mem v B ∧ Rd_entry_d v E f := by
    obtain ⟨s, hsE⟩ := (limit.range E).mp he
    have hs := (limit.projection.bound_l hsE).1
    obtain ⟨a, B₀, pair, atB⟩ := (h.nodes s).mp hs
    have ha := (h.projection.bound_l ((h.index s a B₀ pair).mpr hs)).2
    obtain ⟨o, C, Q, hao, co, hB⟩ := atB
    obtain ⟨n, m, b, d, u, D, i, t, y, U, G, q, C', Q',
      _, _, _, _, _, space, value, dc, fi, id, rt, kdy, measure, family, model⟩ := h.components a o hao
    obtain ⟨ec, eq⟩ := kpair_injective_l M model.code.1 co
    subst C' Q'
    obtain ⟨g, hgq⟩ := (model.map.range B₀).mp hB
    have hg := model.map.projection.input_mem_of_pairMember hgq
    obtain ⟨_, b, fb, gb⟩ := (family g).mp hg
    have hd := space.elim fun v _ => v 0
    have hu := (value.bounds_l I).2.1
    have dΓ := fk.input_mem_of_pairMember kdy
    have ft := fn0_of_function_l (ZF.modelsKP hZF) (rt.isSetFunctionFromTo fk
      (fun x hx => down d x dΓ ((dc x).mp hx).1 ((dc x).mp hx).2))
    obtain ⟨e, pe⟩ := (I).total u b
    obtain ⟨v₁, p₁⟩ := (I).total d e
    obtain ⟨v, pv⟩ := (I).total a v₁
    have actual : Er_count_repr_d I N T Y S k r v E :=
      ⟨a, d, u, b, v₁, e, o, D, i, t, y, U, G, q, C, Q, g, B₀, s,
        pv, p₁, pe, dc, fi, id, rt, ft, kdy, measure, family, model, hg, fb, gb, hgq, pair, hsE⟩
    have hvH := (prod₀ v).mpr ⟨a, ha, v₁, (prod₁ v₁).mpr
      ⟨d, hd, e, (prod₂ e).mpr ⟨u, hu, b, fb.mem_l I, pe⟩, p₁⟩, pv⟩
    have hv := (legal v).mpr ⟨hvH, E, (sat v E).mpr actual⟩
    exact ⟨v, hv, (fs v E).mpr ⟨hv, (sat v E).mpr actual⟩⟩
  exact ZF.ordinal_image_bound_l I hZF (hω.isOrdinal (ZF.modelsKP hZF))
    (small (fun v hv => ((legal v).mp hv).1) ch) ff onto

/-- 活动边的支撑取所属载体中的真实对象码，计数只依赖两侧载体的计数。 -/
theorem It_active_d.countable_l {ω c X R d Y S b j p H U : M.Domain}
    (hω : M.IsOmega ω) (cn : M.CardinalLessOrEqual I X ω) (cy : M.CardinalLessOrEqual I Y ω)
    (mx : Smdl_d I c X R) (my : Smdl_d I d Y S) (target : Smdl_d I b H U)
    (edge : It_active_d hZF ω c d b j p) : M.CardinalLessOrEqual I H ω := by
  obtain ⟨κ, ℓ, F, X', R', Y', S', _, mx', my', w, z, Γ, k, L, J, O, Z, A, q, V, W, r, H', U',
    _, _, agree, length, graph, _, limit, target', _, _⟩ := edge
  obtain ⟨ex, er⟩ := smdl_unique_l I mx' mx
  subst X' R'
  obtain ⟨ey, es⟩ := smdl_unique_l I my' my
  subst Y' S'
  obtain ⟨eh, eu⟩ := smdl_unique_l I target' target
  subst H' U'
  obtain ⟨i, fi⟩ := ZF.exists_inclusionInjection hZF I (fun x hx => ((length x).mp hx).1)
  obtain ⟨s, fs⟩ := cn
  exact er_countable_l hZF hω ⟨s, fs⟩ cy (ZF.exists_compositionInjection hZF I fi fs)
    agree.injection.1 agree.downward graph limit

end YesMetaZFC.SetTheory.LargeCardinal
