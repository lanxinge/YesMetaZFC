import YesMetaZFC.Model.SetTheory.Internal.DirectedSystem.ElementarySyntax

/-! # 初等定向系统的极限保持全部内部公式码

在同时量化所有分量的原公式上归纳。存在量词反向时，把当前分量和目标
见证移到共同后继；该步只用有限定向性，不要求整张 ω 赋值有共同上界。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

theorem di_row_l (hZF : M.Models ZF) {ω J L A p T R q C V K F n r : M.Domain}
    (h : Di_system_d J L A p T R) (limit : Di_limit_d A p T R q C V)
    (elementary : Di_elementary_d (kp_pair_l (ZF.modelsKP hZF)) ω L A p T R)
    (hK : M.IsFunctionSpace (kp_pair_l (ZF.modelsKP hZF)) K ω C)
    (hF : Sfm_d (kp_pair_l (ZF.modelsKP hZF)) ω n F) (hr : M.mem r n) :
    Di_row_d (kp_pair_l (ZF.modelsKP hZF)) ω A p R C V K F n q r := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  have hq := fn0_function_l (ZF.modelsKP hZF) limit.projection
  obtain ⟨H, hH⟩ := seval_exists_l I hZF C V K F hF.2.1.1
  let ρ := (((((((((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push A).push p).push R).push C).push V).push K).push F).push n).push q
  let φ : UnarySchema 10 := {
    body := di_row_m (.bound 10) (.bound 9) (.bound 8) (.bound 7)
      (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have sat t : φ.denote ρ t ↔ Di_row_d I ω A p R C V K F n q t := di_row_sat_l I hZF.1 ..
  apply (sat r).mp (sfm_induction_l I hZF hF φ ρ ?_ hr)
  intro r hr ih
  apply (sat r).mpr
  intro i c X S E stage hE f g hf hg hfg
  obtain ⟨D, hD⟩ := seval_exists_l I hZF X S E F hF.2.1.1
  have ff := (hE f).mp hf
  have point k (hk : M.mem k ω) : ∃ x y, M.PairMember I k x f ∧ M.PairMember I x y q ∧ M.PairMember I k y g := by
    obtain ⟨x, hx, hkx⟩ := ff.2.2 k hk
    obtain ⟨y, _, hxy⟩ := hq.2.2 x (((stage.2.1 x).mp hx).1)
    exact ⟨x, y, hkx, hxy, hfg k hk x y hkx hxy⟩
  have label x k (hkx : M.PairMember I k x f) := ((stage.2.1 x).mp (ff.output_mem_of_pairMember hkx)).2
  obtain ⟨o, ho⟩ := (hF.2.1.2.2 r).mp hr
  rcases hF.2.2 r o ho with ⟨a, b, hs, ha, hb⟩ | ⟨a, b, hs, ha, hb⟩ |
    ⟨a, b, hs, ha, hb⟩ | ⟨a, b, hs, ha, hb⟩
  · obtain ⟨x, u, hax, hxu, hau⟩ := point a ha
    obtain ⟨y, v, hby, hyv, hbv⟩ := point b hb
    have rel : Rd_entry_d x y S ↔ Rd_entry_d u v V := by
      have read : Rd_entry_d x y S ↔ Rd_entry_d x y R := (stage.2.2 x y).trans
        ⟨And.right ∘ And.right, fun hr => ⟨ff.output_mem_of_pairMember hax, ff.output_mem_of_pairMember hby, hr⟩⟩
      exact read.trans ((h.rel_at_l (label x a hax) (label y b hby)
        (h.identity x (h.index.bound_l (label x a hax)).1) (h.identity y (h.index.bound_l (label y b hby)).1)).symm.trans
          (limit.relation x y u v hxu hyv).symm)
    exact (ssat_rel_l I hZF hF hD ho hs hE hf hax hby).trans
      (rel.trans (ssat_rel_l I hZF hF hH ho hs hK hg hau hbv).symm)
  · obtain ⟨x, u, hax, hxu, hau⟩ := point a ha
    obtain ⟨y, v, hby, hyv, hbv⟩ := point b hb
    have eq := ((limit.kernel x y u v hxu hyv).trans (h.eq_at_l (label x a hax) (label y b hby))).symm
    exact (ssat_eq_l I hZF hF hD ho hs hE hf hax hby).trans
      (eq.trans (ssat_eq_l I hZF hF hH ho hs hK hg hau hbv).symm)
  · exact (ssat_nor_l I hZF hF hD ho hs hf).trans ((not_congr (or_congr
      ((sat a).mp (ih a ha) i c X S E stage hE f g hf hg hfg)
      ((sat b).mp (ih b hb) i c X S E stage hE f g hf hg hfg))).trans (ssat_nor_l I hZF hF hH ho hs hg).symm)
  · rw [ssat_exists_l I hZF hF hD ho hs hf, ssat_exists_l I hZF hF hH ho hs hg]
    constructor
    · rintro ⟨x, f', hx, hu, truth⟩
      obtain ⟨y, hy, hxy⟩ := hq.2.2 x (((stage.2.1 x).mp hx).1)
      obtain ⟨g', hv, hgv⟩ := senv_update_exists_l I hZF ((hK g).mp hg) ha hy
      exact ⟨y, g', hy, hv, ((sat b).mp (ih b hb) i c X S E stage hE f' g'
        ((hE f').mpr (hu.function_l I ff ha hx)) ((hK g').mpr hgv)
        (hfg.update_l I hq.1 hxy hu hv)).mp truth⟩
    · rintro ⟨y, g', hy, hv, truth⟩
      -- 新见证在某一分量有代表；共同后继同时容纳它和原赋值的整个分量。
      obtain ⟨v, hvy⟩ := (limit.range y).mp hy
      obtain ⟨j, hj, hvj⟩ := h.index.2.1 v (limit.projection.bound_l hvy).1
      obtain ⟨x, hx⟩ := stage.1.2.1
      have hxi := ((stage.2.1 x).mp hx).2
      obtain ⟨k, _, hik, hjk⟩ := h.order.directed i j (h.index.bound_l hxi).2 hj
      obtain ⟨w, hwk, hvw⟩ := h.total v j k hvj hjk
      obtain ⟨d, Y, W, next⟩ := di_stage_exists_l hZF h hwk
      obtain ⟨e, he, es⟩ := elementary i k c X S d Y W stage next hik
      obtain ⟨f₁, hf₁, assign⟩ := smap_assign_exists_l I hZF he.1.1 ff
      obtain ⟨E₁, hE₁⟩ := ZF.exists_functionSpace hZF I ω Y
      obtain ⟨H₁, hH₁⟩ := seval_exists_l I hZF Y W E₁ F hF.2.1.1
      have hwy : Rd_entry_d w y q := by
        obtain ⟨z, _, hwz⟩ := limit.projection.2.1 w (h.bound v w hvw).2
        exact (limit.commute_l h hvw hvy hwz).symm ▸ hwz
      have projected : Smap_assign_d I ω q f₁ g := by
        intro t ht u z htu huz
        obtain ⟨x, hx, htx⟩ := ff.2.2 t ht
        obtain ⟨u', _, hxu⟩ := he.1.1.2.2 x hx
        have eq := hf₁.1.2 t u' u (assign t ht x u' htx hxu) htu
        subst u'
        obtain ⟨z', _, hxz⟩ := limit.projection.2.1 x (((stage.2.1 x).mp hx).1)
        have eq := limit.commute_l h (((es x u).mp hxu).2.2) hxz huz
        exact hfg t ht x z htx (eq ▸ hxz)
      have hwY := (next.2.1 w).mpr ⟨(h.index.bound_l hwk).1, hwk⟩
      obtain ⟨f₂, update, hf₂⟩ := senv_update_exists_l I hZF hf₁ ha hwY
      have body := ((sat b).mp (ih b hb) k d Y W E₁ next hE₁ f₂ g' ((hE₁ f₂).mpr hf₂)
        ((hK g').mpr (hv.function_l I ((hK g).mp hg) ha hy)) (projected.update_l I hq.1 hwy update hv)).mpr truth
      have future := (ssat_exists_l I hZF hF hH₁ ho hs ((hE₁ f₁).mpr hf₁)).mpr ⟨w, f₂, hwY, update, body⟩
      exact (ssat_exists_l I hZF hF hD ho hs hf).mp
        ((he.ssat_l I hZF.1 stage.1 next.1 hF hr hE hE₁ hf ((hE₁ f₁).mpr hf₁) assign).mpr future)

/-- 每个分量的规范投影都是完整内部初等嵌入。 -/
theorem di_elementary_limit_l (hZF : M.Models ZF) {ω J L A p T R q C V i c X S d : M.Domain}
    (hω : M.IsOmega ω) (h : Di_system_d J L A p T R) (limit : Di_limit_d A p T R q C V)
    (elementary : Di_elementary_d (kp_pair_l (ZF.modelsKP hZF)) ω L A p T R)
    (stage : Di_stage_d (kp_pair_l (ZF.modelsKP hZF)) A p R i c X S)
    (model : Smdl_d (kp_pair_l (ZF.modelsKP hZF)) d C V) :
    ∃ e, Smap_d (kp_pair_l (ZF.modelsKP hZF)) ω c d X C e ∧
      ∀ x y, Rd_entry_d x y e ↔ M.mem x X ∧ Rd_entry_d x y q := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨e, he, spec, _⟩ := di_projection_l hZF h limit stage
  obtain ⟨Z, hZ⟩ := scode_exists_l I hZF hω
  obtain ⟨E, hE⟩ := ZF.exists_functionSpace hZF I ω X
  obtain ⟨K, hK⟩ := ZF.exists_functionSpace hZF I ω C
  refine ⟨e, ⟨he, Z, hZ, fun a f g ha hf hg hfg => ?_⟩, spec⟩
  obtain ⟨n, F, r, hc⟩ := (hZ a).mp ha
  have assign : Smap_assign_d I ω q f g := fun i hi x y hx hy => hfg i hi x y hx
    ((spec x y).mpr ⟨hf.output_mem_of_pairMember hx, hy⟩)
  exact (satisfies_decode_l I hZF.1 stage.1 hc hE).trans
    ((di_row_l hZF h limit elementary hK hc.2.1 hc.2.2 i c X S E stage hE f g ((hE f).mpr hf) ((hK g).mpr hg) assign).trans
      (satisfies_decode_l I hZF.1 model hc hK).symm)

end YesMetaZFC.SetTheory.Internal
