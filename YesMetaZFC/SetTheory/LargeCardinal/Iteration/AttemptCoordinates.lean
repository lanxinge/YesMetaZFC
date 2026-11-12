import YesMetaZFC.SetTheory.LargeCardinal.Iteration.AttemptMember
import YesMetaZFC.SetTheory.LargeCardinal.Cardinals.EmbeddingSetImage

/-! # 可枚举原关系图列的实际初等像

原枚举列属于外层源，故其像仍覆盖每个像载体的全部成员。模型与边
沿实际坐标双射搬运；树序的自然数坐标保持原值。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem it_countable_image_l {ω T Q G E c Z R d U S j : M.Domain}
    (hω : M.IsOmega ω) (tree : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω ω T Q G) (en : Ja_enum_d I ω ω Q E)
    (zt : M.TransitiveSet Z) (ut : M.TransitiveSet U) (mz : Smem_d I c Z R) (mu : Smem_d I d U S)
    (hj : Smap_d I ω c d Z U j) (algebra : Sc_algebra_d Z) (hw : M.mem ω Z)
    (hT : M.mem T Z) (hQ : M.mem Q Z) (hG : M.mem G Z) (hE : M.mem E Z) :
    ∃ Q' G' E', Rd_entry_d T T j ∧ Rd_entry_d Q Q' j ∧ Rd_entry_d G G' j ∧ Rd_entry_d E E' j ∧
      It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω ω T Q' G' ∧ Ja_enum_d I ω ω Q' E' ∧
      (∀ i e', Rd_entry_d i e' E' ↔ ∃ e, Rd_entry_d i e E ∧ Rd_entry_d e e' j) ∧
      (∀ i k f', It_map_d G' i k f' ↔ ∃ f, It_map_d G i k f ∧ Rd_entry_d f f' j) ∧
      ∀ i a A P, Rd_entry_d i a Q → Smdl_d I a A P →
        ∃ b B V f, Rd_entry_d i b Q' ∧ Smdl_d I b B V ∧ Rd_entry_d A B j ∧
          Smap_d I ω b a B A f ∧ ∀ y x, Rd_entry_d y x f ↔ M.mem x A ∧ Rd_entry_d x y j := by
  have natural := hj.natural_l hZF hω zt ut mz mu hw
  have omega := hj.omega_l I hZF hω zt ut mz mu hw
  have order := hj.fixed_relation_l hZF hω zt ut mz mu omega natural hT ⟨tree.order.relation, tree.order.bound⟩
  have pairs r (hr : M.mem r T) : Rd_entry_d r r j := by
    obtain ⟨i, k, pair⟩ := tree.order.relation r hr
    have bounds := tree.order.bound i k ⟨r, pair, hr⟩
    exact hj.fixed_pair_l hZF hω zt ut mz mu (zt T hT r hr) pair (natural i bounds.1) (natural k bounds.2)
  -- 列的值不必固定；固定指标及函数性逐项确定原列与像列。
  have column {D F} (hD : Rd_entry_d D D j) (point : ∀ x, M.mem x D → Rd_entry_d x x j)
      (hF : M.mem F Z) (ff : M.IsSetFunction I F) (dom : M.IsDomainOf I D F) :
      ∃ F', Rd_entry_d F F' j ∧ M.IsSetFunction I F' ∧ M.IsDomainOf I D F' ∧
        ∀ i y, Rd_entry_d i y F' ↔ ∃ x, Rd_entry_d i x F ∧ Rd_entry_d x y j := by
    obtain ⟨A, hA, bounds⟩ := algebra.envelope_l hF
    have fn : Fn0_d D A F := fn0_of_function_l (ZF.modelsKP hZF) ⟨ff, dom, fun x hx => by
      obtain ⟨y, hxy⟩ := (dom x).mp hx
      exact ⟨y, (bounds x y hxy).2, hxy⟩⟩
    obtain ⟨B, _, hAB⟩ := hj.1.1.2.2 A hA
    obtain ⟨F', _, hFF⟩ := hj.1.1.2.2 F hF
    have image := (hj.function_l hZF hω zt ut mz mu hD hAB hFF).mp fn
    refine ⟨F', hFF, (fn0_function_l (ZF.modelsKP hZF) image).1,
      (fn0_function_l (ZF.modelsKP hZF) image).2.1, fun i y => ⟨?_, ?_⟩⟩
    · intro hiy
      obtain ⟨x, hx, hix⟩ := fn.2.1 i (image.bound_l hiy).1
      obtain ⟨y', _, hxy⟩ := hj.1.1.2.2 x (zt A hA x hx)
      have hiy' := (hj.entry_l hZF hω zt ut mz mu (point i (image.bound_l hiy).1) hxy hFF).mp hix
      exact ⟨x, hix, image.2.2 i (image.bound_l hiy).1 y' (image.bound_l hiy').2 y (image.bound_l hiy).2 hiy' hiy ▸ hxy⟩
    · rintro ⟨x, hix, hxy⟩
      exact (hj.entry_l hZF hω zt ut mz mu (point i (fn.bound_l hix).1) hxy hFF).mp hix
  obtain ⟨Q', qq, qf, qd, qs⟩ := column omega natural hQ tree.model_function tree.model_domain
  obtain ⟨G', gg, gf, gd, gs⟩ := column order pairs hG tree.map_function tree.map_domain
  obtain ⟨E', ee, ef, ed, es⟩ := column omega natural hE en.function en.domain
  have edge i k f' : It_map_d G' i k f' ↔ ∃ f, It_map_d G i k f ∧ Rd_entry_d f f' j := by
    constructor
    · rintro ⟨r, pair, hr⟩
      obtain ⟨f, hf, hff⟩ := (gs r f').mp hr
      exact ⟨f, ⟨r, pair, hf⟩, hff⟩
    · rintro ⟨f, ⟨r, pair, hr⟩, hff⟩
      exact ⟨r, pair, (gs r f').mpr ⟨f, hr, hff⟩⟩
  have model {i a A P b} (ha : Rd_entry_d i a Q) (ma : Smdl_d I a A P) (hab : Rd_entry_d a b j) :
      ∃ B V f g, Smdl_d I b B V ∧ Rd_entry_d A B j ∧ Rd_entry_d P V j ∧
        M.IsSetBijectionFromTo I f A B ∧ Smap_d I ω a b A B f ∧ Smap_d I ω b a B A g ∧
        (∀ x y, Rd_entry_d x y f ↔ M.mem x A ∧ Rd_entry_d x y j) ∧
        (∀ y x, Rd_entry_d y x g ↔ Rd_entry_d x y f) ∧
        ∀ e e', Rd_entry_d i e E → Rd_entry_d e e' j →
          Fn0_d ω B e' ∧ ∀ y, M.mem y B → ∃ n, M.mem n ω ∧ Rd_entry_d n y e' := by
    have own := ma.1.mem_l M zt (rd_entry_transitive_l zt hQ ha).2
    obtain ⟨B, _, hAB⟩ := hj.1.1.2.2 A own.1
    obtain ⟨V, _, hPV⟩ := hj.1.1.2.2 P own.2
    have enumeration {e e'} (he : Rd_entry_d i e E) (hee : Rd_entry_d e e' j) :
        Fn0_d ω B e' ∧ ∀ y, M.mem y B → ∃ n, M.mem n ω ∧ Rd_entry_d n y e' := by
      have row := en.rows i e a A P he ha ma.1
      have fn := (hj.function_l hZF hω zt ut mz mu omega hAB hee).mp row.1
      let φ : Formula 1 3 := Formula.forallMem (.bound 1)
        (Formula.existsMem (.bound 3) (rd_entry0_m .newest (.bound 1) (.bound 2)))
      have tr := smap_delta_l I hZF hω zt ut mz mu hj φ (by simp -implicitDefEqProofs [φ])
        (.forallMem _ (.existsMem _ (rd_entry0_delta_l ..)))
        ⟨Fin.cases e (Fin.cases A (fun _ => ω)), fun _ => ω⟩
        ⟨Fin.cases e' (Fin.cases B (fun _ => ω)), fun _ => ω⟩ (Fin.cases hee (Fin.cases hAB (fun _ => omega)))
      simp only [φ, Formula.satisfies_forallMem_iff, Formula.satisfies_existsMem_iff, rd_entry0_sat_l hZF.1] at tr
      exact ⟨fn, tr.mp row.2⟩
    have onto y (hy : M.mem y B) : ∃ x, M.mem x A ∧ Rd_entry_d x y j := by
      obtain ⟨e, he⟩ := (en.domain i).mp ((tree.model_domain i).mpr ⟨a, ha⟩)
      obtain ⟨e', _, hee⟩ := hj.1.1.2.2 e (rd_entry_transitive_l zt hE he).2
      obtain ⟨fn, cover⟩ := enumeration he hee
      obtain ⟨n, hn, hny⟩ := cover y hy
      obtain ⟨x, hx, hnx⟩ := (en.rows i e a A P he ha ma.1).1.2.1 n hn
      obtain ⟨y', _, hxy⟩ := hj.1.1.2.2 x (zt A own.1 x hx)
      have hny' := (hj.entry_l hZF hω zt ut mz mu (natural n hn) hxy hee).mp hnx
      exact ⟨x, hx, fn.2.2 n hn y' (fn.bound_l hny').2 y hy hny' hny ▸ hxy⟩
    obtain ⟨f, g, mb, bij, forward, backward, fs, gs⟩ := ep_set_iso_image_l hZF hω zt ut mz mu hj ma hab hAB hPV onto
    exact ⟨B, V, f, g, mb, hAB, hPV, bij, forward, backward, fs, gs, fun e e' => enumeration⟩
  have models i b (hb : Rd_entry_d i b Q') : ∃ B V, Smdl_d I b B V := by
    obtain ⟨a, ha, hab⟩ := (qs i b).mp hb
    obtain ⟨A, P, ma⟩ := tree.models i a ha
    obtain ⟨B, V, _, _, mb, _⟩ := model ha ma hab
    exact ⟨B, V, mb⟩
  have diagram : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω ω T Q' G' := by
    refine ⟨tree.order, qf, qd, models, gf, gd, ?_, ?_, ?_⟩
    · intro i k f' a' A' P' b' B' V' hf' ha' hb' ma' mb'
      obtain ⟨f, hf, hff⟩ := (edge i k f').mp hf'
      obtain ⟨a, ha, haa⟩ := (qs i a').mp ha'
      obtain ⟨b, hb, hbb⟩ := (qs k b').mp hb'
      obtain ⟨A, P, ma⟩ := tree.models i a ha
      obtain ⟨B, V, mb⟩ := tree.models k b hb
      obtain ⟨A₀, P₀, r, s, ma₀, aa, pp, bij, forward, back, rs, ss, _⟩ := model ha ma haa
      obtain ⟨B₀, V₀, t, u, mb₀, bb, vv, _, target, _, ts, _, _⟩ := model hb mb hbb
      obtain ⟨ea, ep⟩ := smdl_unique_l I ma₀ ma'
      subst A₀ P₀
      obtain ⟨eb, ev⟩ := smdl_unique_l I mb₀ mb'
      subst B₀ V₀
      have old := tree.elementary i k f a A P b B V hf ha hb ma mb
      have fn := (hj.function_l hZF hω zt ut mz mu aa bb hff).mp (fn0_of_function_l (ZF.modelsKP hZF) old.1.1)
      obtain ⟨v, hv, vs⟩ := smap_comp_l I hZF back old
      obtain ⟨w, hw, ws⟩ := smap_comp_l I hZF hv target
      have eq := (fn0_of_function_l (ZF.modelsKP hZF) hw.1.1).ext_l hZF.1 fn (fun x hx => by
        obtain ⟨x₀, hx₀, hxx⟩ := bij.2 x hx
        obtain ⟨y₀, hy₀, hxy⟩ := old.1.1.2.2 x₀ hx₀
        obtain ⟨y, _, hyy⟩ := target.1.1.2.2 y₀ hy₀
        exact ⟨y, (ws x y).mpr ⟨hx, y₀, (vs x y₀).mpr ⟨hx, x₀, (ss x x₀).mpr hxx, hxy⟩, hyy⟩,
          (hj.entry_l hZF hω zt ut mz mu ((rs x₀ x).mp hxx).2 ((ts y₀ y).mp hyy).2 hff).mp hxy⟩)
      exact eq ▸ hw
    · intro i f' hf' x y hxy
      obtain ⟨f, hf, hff⟩ := (edge i i f').mp hf'
      obtain ⟨a, A, P, ha, ma⟩ := tree.model_l hZF (tree.order.bound i i (tree.map_bound_l hZF hf)).1
      obtain ⟨a', _, haa⟩ := hj.1.1.2.2 a (rd_entry_transitive_l zt hQ ha).2
      obtain ⟨B, V, r, s, mb, ab, _, bij, _, _, rs, _, _⟩ := model ha ma haa
      have fn := (hj.function_l hZF hω zt ut mz mu ab ab hff).mp
        (fn0_of_function_l (ZF.modelsKP hZF) (tree.elementary i i f a A P a A P hf ha ha ma ma).1.1)
      obtain ⟨x₀, hx₀, hxx⟩ := bij.2 x (fn.bound_l hxy).1
      obtain ⟨y₀, hy₀, hyy⟩ := bij.2 y (fn.bound_l hxy).2
      have eq := tree.identity i f hf x₀ y₀
        ((hj.entry_l hZF hω zt ut mz mu ((rs x₀ x).mp hxx).2 ((rs y₀ y).mp hyy).2 hff).mpr hxy)
      exact hj.1.1.1.2 y₀ x y (eq ▸ ((rs x₀ x).mp hxx).2) ((rs y₀ y).mp hyy).2
    · intro i k l f' g' h' hf' hg' hh' x y z hxy hyz
      obtain ⟨f, hf, ff⟩ := (edge i k f').mp hf'
      obtain ⟨g, hg, gg₀⟩ := (edge k l g').mp hg'
      obtain ⟨h, hh, hh₀⟩ := (edge i l h').mp hh'
      have point i : ∀ a A P, Rd_entry_d i a Q → Smdl_d I a A P →
          ∃ a' B V r s, Smdl_d I a' B V ∧ Rd_entry_d A B j ∧ Rd_entry_d P V j ∧
            M.IsSetBijectionFromTo I r A B ∧ Smap_d I ω a a' A B r ∧ Smap_d I ω a' a B A s ∧
            (∀ v w, Rd_entry_d v w r ↔ M.mem v A ∧ Rd_entry_d v w j) := by
        intro a A P ha ma
        obtain ⟨a', _, haa⟩ := hj.1.1.2.2 a (rd_entry_transitive_l zt hQ ha).2
        obtain ⟨B, V, r, s, mb, ab, pv, bij, forward, back, rs, _⟩ := model ha ma haa
        exact ⟨a', B, V, r, s, mb, ab, pv, bij, forward, back, rs⟩
      obtain ⟨a, A, P, ha, ma⟩ := tree.model_l hZF (tree.order.bound i k (tree.map_bound_l hZF hf)).1
      obtain ⟨b, B, V, hb, mb⟩ := tree.model_l hZF (tree.order.bound i k (tree.map_bound_l hZF hf)).2
      obtain ⟨c, C, W, hc, mc⟩ := tree.model_l hZF (tree.order.bound k l (tree.map_bound_l hZF hg)).2
      obtain ⟨a', A', P', r, _, _, aa, _, ar, _, _, rs⟩ := point i a A P ha ma
      obtain ⟨b', B', V', s, _, _, bb, _, bs, _, _, ss⟩ := point k b B V hb mb
      obtain ⟨c', C', W', t, _, _, cc, _, ct, _, _, ts⟩ := point l c C W hc mc
      have fn := (hj.function_l hZF hω zt ut mz mu aa bb ff).mp
        (fn0_of_function_l (ZF.modelsKP hZF) (tree.elementary i k f a A P b B V hf ha hb ma mb).1.1)
      have gn := (hj.function_l hZF hω zt ut mz mu bb cc gg₀).mp
        (fn0_of_function_l (ZF.modelsKP hZF) (tree.elementary k l g b B V c C W hg hb hc mb mc).1.1)
      obtain ⟨x₀, _, hx⟩ := ar.2 x (fn.bound_l hxy).1
      obtain ⟨y₀, _, hy⟩ := bs.2 y (fn.bound_l hxy).2
      obtain ⟨z₀, _, hz⟩ := ct.2 z (gn.bound_l hyz).2
      have xx := ((rs x₀ x).mp hx).2
      have yy := ((ss y₀ y).mp hy).2
      have zz := ((ts z₀ z).mp hz).2
      exact (hj.entry_l hZF hω zt ut mz mu xx zz hh₀).mp
        (tree.comp i k l f g h hf hg hh x₀ y₀ z₀
          ((hj.entry_l hZF hω zt ut mz mu xx yy ff).mpr hxy) ((hj.entry_l hZF hω zt ut mz mu yy zz gg₀).mpr hyz))
  have enumeration : Ja_enum_d I ω ω Q' E' := by
    refine ⟨ef, ed, ?_⟩
    intro i e' b B V he' hb pair
    obtain ⟨e, he, hee⟩ := (es i e').mp he'
    obtain ⟨a, ha, hab⟩ := (qs i b).mp hb
    obtain ⟨A, P, ma⟩ := tree.models i a ha
    obtain ⟨B₀, V₀, _, _, mb, _, _, _, _, _, _, _, rows⟩ := model ha ma hab
    obtain ⟨eb, ev⟩ := kpair_injective_l M mb.1 pair
    subst B₀ V₀
    exact rows e e' he hee
  refine ⟨Q', G', E', order, qq, gg, ee, diagram, enumeration, es, edge, ?_⟩
  intro i a A P ha ma
  obtain ⟨b, _, hab⟩ := hj.1.1.2.2 a (rd_entry_transitive_l zt hQ ha).2
  obtain ⟨B, V, f, g, mb, ab, _, _, _, back, fs, gs, _⟩ := model ha ma hab
  exact ⟨b, B, V, g, (qs i b).mpr ⟨a, ha, hab⟩, mb, ab, back, fun y x => (gs y x).trans (fs x y)⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 移动模型坐标下的同一有限尝试值

像枚举以同一自然数读取原元素的像，像树边保持实际求值方程。
末端先沿坐标逆图回收再施加原嵌入，因此每个有限尝试值完全相同。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ja_value_image_l {ω T Q G E Q' G' E' c Z R d U S j k a X P a' X' P' A π s t : M.Domain}
    (hω : M.IsOmega ω) (tree : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω ω T Q G) (image : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω ω T Q' G')
    (en : Ja_enum_d I ω ω Q E) (en' : Ja_enum_d I ω ω Q' E')
    (zt : M.TransitiveSet Z) (ut : M.TransitiveSet U) (mz : Smem_d I c Z R) (mu : Smem_d I d U S)
    (hj : Smap_d I ω c d Z U j) (hw : M.mem ω Z) (hG : M.mem G Z) (hE : M.mem E Z)
    (es : ∀ i e', Rd_entry_d i e' E' ↔ ∃ e, Rd_entry_d i e E ∧ Rd_entry_d e e' j)
    (maps : ∀ i k f', It_map_d G' i k f' ↔ ∃ f, It_map_d G i k f ∧ Rd_entry_d f f' j)
    (ha : Rd_entry_d k a Q) (ma : Smdl_d I a X P) (ha' : Rd_entry_d k a' Q') (ma' : Smdl_d I a' X' P')
    (fp : Fn0_d X A π) (inverse : ∀ v x, Rd_entry_d v x s ↔ M.mem x X ∧ Rd_entry_d x v j)
    (comp : It_comp_d s π t) :
    ∀ i n y, M.mem n ω → (Ja_value_d G' E' k t i n y ↔ Ja_value_d G E k π i n y) := by
  have nat := hj.natural_l hZF hω zt ut mz mu hw
  have ownf {i f} (hf : It_map_d G i k f) : M.mem f Z :=
    hf.elim fun _ h => (rd_entry_transitive_l zt hG h.2).2
  have shift {i n e f e' f' x v} (hn : M.mem n ω) (he : Rd_entry_d i e E) (hf : It_map_d G i k f)
      (ee : Rd_entry_d e e' j) (ff : Rd_entry_d f f' j) (hnx : Rd_entry_d n x e) (hxv : Rd_entry_d x v f) :
      ∃ x' v', Rd_entry_d x x' j ∧ Rd_entry_d v v' j ∧ Rd_entry_d n x' e' ∧ Rd_entry_d x' v' f' := by
    obtain ⟨x', _, xx⟩ := hj.1.1.2.2 x (rd_entry_transitive_l zt (rd_entry_transitive_l zt hE he).2 hnx).2
    obtain ⟨v', _, vv⟩ := hj.1.1.2.2 v (rd_entry_transitive_l zt (ownf hf) hxv).2
    exact ⟨x', v', xx, vv, (hj.entry_l hZF hω zt ut mz mu (nat n hn) xx ee).mp hnx,
      (hj.entry_l hZF hω zt ut mz mu xx vv ff).mp hxv⟩
  intro i n y hn
  constructor
  · rintro ⟨e', f', x', v', he', hf', hnx', hxv', hvy⟩
    obtain ⟨e, he, ee⟩ := (es i e').mp he'
    obtain ⟨f, hf, ff⟩ := (maps i k f').mp hf'
    have hi := (tree.order.bound i k (tree.map_bound_l hZF hf)).1
    obtain ⟨b, B, V, hb, mb⟩ := tree.model_l hZF hi
    obtain ⟨b', B', V', hb', mb'⟩ := image.model_l hZF hi
    have ef := (en.rows i e b B V he hb mb.1).1
    have ef' := (en'.rows i e' b' B' V' he' hb' mb'.1).1
    have old := tree.elementary i k f b B V a X P hf hb ha mb ma
    have new := image.elementary i k f' b' B' V' a' X' P' hf' hb' ha' mb' ma'
    obtain ⟨x, hx, hnx⟩ := ef.2.1 n hn
    obtain ⟨v, _, hxv⟩ := old.1.1.2.2 x hx
    obtain ⟨x₁, v₁, xx, vv, hnx₁, hxv₁⟩ := shift hn he hf ee ff hnx hxv
    have ex := ef'.2.2 n hn x₁ (ef'.bound_l hnx₁).2 x' (ef'.bound_l hnx').2 hnx₁ hnx'
    have ev := new.1.1.1.2 x' v₁ v' (ex ▸ hxv₁) hxv'
    obtain ⟨v₀, hv₀, hv₀y⟩ := (comp.2 v' y).mp hvy
    have eq := hj.1.2 v₀ v v' ((inverse v' v₀).mp hv₀).2 (ev ▸ vv)
    exact ⟨e, f, x, v, he, hf, hnx, hxv, eq ▸ hv₀y⟩
  · rintro ⟨e, f, x, v, he, hf, hnx, hxv, hvy⟩
    obtain ⟨e', _, ee⟩ := hj.1.1.2.2 e (rd_entry_transitive_l zt hE he).2
    obtain ⟨f', _, ff⟩ := hj.1.1.2.2 f (ownf hf)
    obtain ⟨x', v', _, vv, hnx', hxv'⟩ := shift hn he hf ee ff hnx hxv
    exact ⟨e', f', x', v', (es i e').mpr ⟨e, he, ee⟩, (maps i k f').mpr ⟨f, hf, ff⟩, hnx', hxv',
      (comp.2 v' y).mpr ⟨v, (inverse v' v).mpr ⟨(fp.bound_l hvy).1, vv⟩, hvy⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal
