import YesMetaZFC.SetTheory.LargeCardinal.ExtenderRawRelation
import YesMetaZFC.Model.SetTheory.Internal.EmbeddingRelative

/-! # 下一共同低层的完整前驱实现

所属源的同一有界池直接投影到新原关系极限。精确关系与全部前驱覆盖
确定其传递值的唯一实现；整个新极限始终保持未坍塌。
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

section Low
variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Eb_collapse_d.next_raw_l {ω c X R c' Y S q H N κ K L F R₀ Γ γ k J O Z A p T V r o C W j
    B₀ b D₀ a₀ f₀ H₀ D₁ Q₁ Γ₁ e : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (mx : Smem_d I c X R)
    (theory : Sc_theory_d I ω X R) (model : Smdl_d I c' Y S) (hq : Smap_d I ω c c' X Y q)
    (closed : Rr_closed_d I Y S H)
    (owner : Ep_source_d hZF ω κ K N R₀) (hΓ : M.mem Γ N) (rank : Vr_d N γ Γ) (hγ : M.IsLimitOrdinal γ)
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
  have low := rank.transitive_l hZF owner.transitive hΓ
  have hB₀ := fk.1.input_mem_of_pairMember hBb
  have sub := low B₀ hB₀
  have key := fn0_of_function_l (ZF.modelsKP hZF) fk.1
  -- 同一有界池的每个节点取得唯一原关系极限值，故可直接替换成实际求值图。
  let η : Env M 5 := ⟨Fin.cases r (Fin.cases k (Fin.cases Y (Fin.cases Γ (fun _ => κ)))), fun _ => κ⟩
  let φ : BinarySchema 5 := { body := er_value_m (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have sat u E : φ.denote η u E ↔ Er_value_d κ Γ Y k r u E := er_value_sat_l hZF.1 ..
  have total u (hu : M.mem u D₁) : ∃ E, φ.denote η u E := by
    obtain ⟨n, a, D, f, _, ha, fa, ds, hf, ff, pair⟩ := pool.read_l hZF owner hu
    obtain ⟨g, E, comp, value⟩ := system.bounded_value_l hZF hω hX mx model hq closed owner.transitive owner.theory.algebra
      hΓ rank hγ fk image pred family limit hBb ha fa ds hf ff
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
    obtain ⟨m, a₁, D₂, f₁, hm, _, fa, ds, _, ff₁, pair₁⟩ := pool.read_l hZF owner hu
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
    obtain ⟨n, a, D, f, hn, ha, fa, ds, hf, ff, pair⟩ := pool.read_l hZF owner hu
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
      (link.trans (er_edge_iff_l hZF owner family system limit fk sub pred membership (fun a U h => (range U).mpr ⟨a, h⟩)
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
        owner.transitive owner.theory.algebra hΓ rank hγ fk image pred family limit hBb ff₀ constant fv edge
      obtain ⟨u, pair⟩ := (I).total a f
      have hu := pool.node_l hZF owner hn ha fa ds hf ff pair
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
  obtain ⟨k', fk', graph, _, predecessor⟩ := collapse.realize_l hZF reflect (fn0_of_function_l (ZF.modelsKP hZF) vf)
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
    (owner : Ep_source_d hZF ω κ K N R₀) (hΓ : M.mem Γ N) (rank : Vr_d N γ Γ)
    (hγ : M.IsLimitOrdinal γ) (hκ : M.mem κ Γ)
    (fk : M.IsSetInjectionFromTo I k Γ Y)
    (image : ∀ z, Rd_entry_d z H S ↔ ∃ x, M.mem x Γ ∧ Rd_entry_d x z k)
    (pred : ∀ x z, Rd_entry_d x z k → ∀ w, Rd_entry_d w z S ↔ ∃ y, M.mem y x ∧ Rd_entry_d y w k)
    (family : Em_source_d ω κ L N F)
    (coherent : Ec_source_d I ω κ L N F)
    (above : M.MemberSubset ω L) (hB₀ : M.mem B₀ Γ) (trans₀ : M.TransitiveSet B₀)
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
  obtain ⟨J, O, Z, A, p, T, V, r, o, C, W, j, q', system, limit, next, elem, embed, root, certificate, comp, a₀, D₀, _, _, constants⟩ :=
    er_ultrapower_l hZFC hω hX mx theory collection model hq small closed owner hΓ rank hγ hκ fk image pred family coherent above
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
