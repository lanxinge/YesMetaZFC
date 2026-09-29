import YesMetaZFC.Model.Forcing.InternalCCC
import YesMetaZFC.Model.Forcing.InternalZF

/-! # 可数链条件的基数界反射

泛型商中的单射名称不能把一个旧集合压到更小的旧无限基数。先排除可定义的
双原像碰撞，再为每个可能原像选择一个条件；这些条件形成内部反链，故每个
旧目标元素只有可数多个可能原像。最后在地模型中取这些可数集合的并。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable (M : SetTheory.Structure.{u})

def Value_d (B R z b f p x y : M.Domain) : Prop :=
  ∃ a s, KPair_d M a x y ∧ Check_d M b a s ∧ Mem_force_d M B R z p s f

def value_m {n} (B R z b f p x y : Term n) : Formula 1 n :=
  .existsE (.existsE (.conj (kpair_m (.bound 1) x.weaken.weaken y.weaken.weaken)
    (.conj (check_m b.weaken.weaken (.bound 1) .newest)
      (mem_force_m B.weaken.weaken R.weaken.weaken z.weaken.weaken p.weaken.weaken .newest f.weaken.weaken))))
derive_free_closed value_m

theorem value_sat_l (hE : Extensional M) {n} (ρ : Env M n) (B R z b f p x y : Term n) :
    Formula.satisfies ρ (value_m B R z b f p x y) ↔
      Value_d M (B.eval ρ) (R.eval ρ) (z.eval ρ) (b.eval ρ) (f.eval ρ) (p.eval ρ) (x.eval ρ) (y.eval ρ) := by
  simp only [value_m, Value_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    kpair_sat_l M hE, check_sat_l M hE, mem_force_sat_l M hE,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken,
    Term.eval_bound_one_push, Term.eval_bound_zero_push]

def Collision_d (B R z b f X Y p : M.Domain) : Prop :=
  ∃ x y v, M.mem x X ∧ M.mem y Y ∧ M.mem v Y ∧ y ≠ v ∧
    Value_d M B R z b f p y x ∧ Value_d M B R z b f p v x

def collision_m {n} (B R z b f X Y p : Term n) : Formula 1 n :=
  .existsE (.existsE (.existsE (.conj (.mem (.bound 2) X.weaken.weaken.weaken)
    (.conj (.mem (.bound 1) Y.weaken.weaken.weaken) (.conj (.mem .newest Y.weaken.weaken.weaken)
      (.conj (.neg (Formula.extensionalEq (.bound 1) .newest))
        (.conj (value_m B.weaken.weaken.weaken R.weaken.weaken.weaken z.weaken.weaken.weaken
          b.weaken.weaken.weaken f.weaken.weaken.weaken p.weaken.weaken.weaken (.bound 1) (.bound 2))
          (value_m B.weaken.weaken.weaken R.weaken.weaken.weaken z.weaken.weaken.weaken
            b.weaken.weaken.weaken f.weaken.weaken.weaken p.weaken.weaken.weaken .newest (.bound 2)))))))))
derive_free_closed collision_m

theorem collision_sat_l (hE : Extensional M) {n} (ρ : Env M n) (B R z b f X Y p : Term n) :
    Formula.satisfies ρ (collision_m B R z b f X Y p) ↔
      Collision_d M (B.eval ρ) (R.eval ρ) (z.eval ρ) (b.eval ρ) (f.eval ρ) (X.eval ρ) (Y.eval ρ) (p.eval ρ) := by
  simp only [collision_m, Collision_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_neg_iff, Formula.satisfies_extensionalEq_iff_eq hE,
    value_sat_l M hE, Definitional.Term.eval_newest, Definitional.Term.eval_weaken,
    Term.eval_bound_two_push, Term.eval_bound_one_push, Term.eval_bound_zero_push]

variable {M} {B R z : M.Domain} (O : Cond_order_d M B R z)
include O

theorem value_lower_l (b f x y : M.Domain) : Lower_d M B R z (fun p => Value_d M B R z b f p x y) := by
  rintro p q hp hq ⟨a, s, ha, hs, hmem⟩
  exact ⟨a, s, ha, hs, (regular_mem_l O s f).1 p q hp hq hmem⟩

theorem value_truth_l (hZF : M.Models ZF) {U : M.Domain → Prop} (hU : Generic_d M B R z U)
    {b f} (hb : U b) (e : M.Domain → (extension_l M hZF B R z U).Domain)
    (he : ∀ a y, y ∈ e a ↔ ∃ c, M.mem c a ∧ e c = y)
    (hv : ∀ a s, Check_d M b a s → Qval_d M B R z U s (e a))
    {F} (hf : Qval_d M B R z U f F) (x y : M.Domain) :
    (∃ p, U p ∧ Value_d M B R z b f p x y) ↔
      Entry_d (extension_l M hZF B R z U) (e x) (e y) F := by
  let E := extension_l M hZF B R z U
  constructor
  · rintro ⟨p, hp, a, s, ha, hs, hmem⟩
    exact ⟨e a, image_kpair_l e he ha, (qval_mem_forcing_l O hZF hU (hv a s hs) hf).mp ⟨p, hp, hmem⟩⟩
  · rintro ⟨v, hvp, hvF⟩
    obtain ⟨a, ha⟩ := (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))).total x y
    have hve : v = e a := kpair_unique_l E (extension_ext_l O hZF hU) hvp (image_kpair_l e he ha)
    obtain ⟨s, hs, _, _⟩ := zf_check_l M hZF (hU.proper b hb).1 a
    obtain ⟨p, hp, hmem⟩ := (qval_mem_forcing_l O hZF hU (hv a s hs) hf).mpr (hve ▸ hvF)
    exact ⟨p, hp, a, s, ha, hs, hmem⟩

/-- 排除碰撞的一个条件下，每个旧值的可能原像集合在地模型内可数。 -/
theorem ccc_fiber_l (hZFC : M.Models ZFC) {ω}
    (hc : Ccc_d M (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) ω B R z)
    {b f p X Y x D} (hp : M.mem p B) (hx : M.mem x X)
    (hn : Neg_d M B R z (Collision_d M B R z b f X Y) p)
    (hD : ∀ y, M.mem y D ↔ M.mem y Y ∧ ∃ q, Below_d M B R z q p ∧ Value_d M B R z b f q y x) :
    M.CardinalLessOrEqual (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) D ω := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  let ρ : Env M 7 := ((((((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z).push b).push f).push p).push x
  let φ : BinarySchema 7 := {
    body := .conj (below_m (.bound 8) (.bound 7) (.bound 6) .newest (.bound 3))
      (value_m (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 4) .newest (.bound 1) (.bound 2)) }
  have hφ y q : φ.denote ρ y q ↔ Below_d M B R z q p ∧ Value_d M B R z b f q y x := by
    simp only [BinarySchema.denote, φ, Formula.satisfies_conj_iff, below_sat_l M hZF.1, value_sat_l M hZF.1]
    rfl
  obtain ⟨g, hg, hgp⟩ := ZFC.uniformize_formula_l I hZFC φ ρ (X := D) (Y := B) (by
    intro y hy
    obtain ⟨_, q, hq, hv⟩ := (hD y).mp hy
    exact ⟨q, hq.1, (hφ y q).mpr ⟨hq, hv⟩⟩)
  have hgq {y q} (h : M.PairMember I y q g) := (hφ y q).mp (hgp y q h)
  have hu {y v q r} (hy : M.PairMember I y q g) (hv : M.PairMember I v r g)
      (hqr : Cmp_d M B R z q r) : y = v := by
    classical
    apply Classical.byContradiction
    intro hyv
    obtain ⟨w, hwq, hwr⟩ := hqr
    have hqp := (hgq hy).1
    have hrp := (hgq hv).1
    apply hn w (below_trans_l O hp hwq hqp)
    exact ⟨x, y, v, hx, ((hD y).mp (hg.input_mem_of_pairMember hy)).1,
      ((hD v).mp (hg.input_mem_of_pairMember hv)).1, hyv,
      value_lower_l O b f y x q w hqp.1 hwq (hgq hy).2,
      value_lower_l O b f v x r w hrp.1 ⟨hwq.1, hwq.2.1, hwr⟩ (hgq hv).2⟩
  obtain ⟨A, hA⟩ := ZF.exists_range_of_setFunction hZF I hg.1 hg.2.1
  have hanti : Antichain_d M B R z A := by
    refine ⟨fun q hq => ?_, fun q r hq hr hqr => ?_⟩
    · obtain ⟨y, hy⟩ := (hA q).mp hq
      exact ⟨(hgq hy).1.1, (hgq hy).1.2.1⟩
    · obtain ⟨y, hy⟩ := (hA q).mp hq
      obtain ⟨v, hv⟩ := (hA r).mp hr
      exact hg.1.2 y q r hy (hu hy hv hqr ▸ hv)
  have hginj : M.IsSetInjectionFromTo I g D A := by
    refine ⟨⟨hg.1, hg.2.1, fun y hy => ?_⟩, fun y v q hy hv => ?_⟩
    · obtain ⟨q, _, hyq⟩ := hg.2.2 y hy
      exact ⟨q, (hA q).mpr ⟨y, hyq⟩, hyq⟩
    · have hq := (hgq hy).1
      exact hu hy hv ⟨q, below_refl_l O hq.1 hq.2.1, O.refl q hq.1⟩
  obtain ⟨F, hF⟩ := hc A hanti
  exact ZF.exists_compositionInjection hZF I hginj hF

variable (hZFC : M.Models ZFC) {U : M.Domain → Prop} (hU : Generic_d M B R z U)
local notation "E" => extension_l M (ZFC.models_zf_l hZFC) B R z U
local notation "J" => kpair_interpretation_l E (extension_ext_l O (ZFC.models_zf_l hZFC) hU)
  (internal_pair_l O (ZFC.models_zf_l hZFC) hU)
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))
include hZFC hU

/-- 扩张中的旧集合单射给出地模型内的 κ² 基数界。 -/
theorem ccc_injection_bound_l {ω κ X Y W b}
    (hc : Ccc_d M I ω B R z) (hb : U b) (hωκ : M.CardinalLessOrEqual I ω κ)
    (hX : M.CardinalLessOrEqual I X κ) (hW : M.IsCartesianProduct I W κ κ)
    (e : M.Domain → (E).Domain) (hi : Function.Injective e)
    (he : ∀ a y, y ∈ e a ↔ ∃ c, M.mem c a ∧ e c = y)
    (hv : ∀ a s, Check_d M b a s → Qval_d M B R z U s (e a))
    {F} (hf : (E).IsSetInjectionFromTo J F (e Y) (e X)) : M.CardinalLessOrEqual I Y W := by
  let hZF := ZFC.models_zf_l hZFC
  obtain ⟨f, _, hF⟩ := value_name_l F
  let ρ : Env M 7 := ((((((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z).push b).push f).push X).push Y
  let ν : UnarySchema 7 := {
    body := collision_m (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have hν : Defined_d M (Collision_d M B R z b f X Y) :=
    ⟨7, ν, ρ, fun p => collision_sat_l M hZF.1 (ρ.push p) _ _ _ _ _ _ _ _⟩
  have hn : ¬ ∃ p, U p ∧ Collision_d M B R z b f X Y p := by
    rintro ⟨p, hp, x, y, v, _, _, _, hyv, hxy, hxv⟩
    exact hyv (hi (hf.2 (e y) (e v) (e x)
      ((value_truth_l O hZF hU hb e he hv hF y x).mp ⟨p, hp, hxy⟩)
      ((value_truth_l O hZF hU hb e he hv hF v x).mp ⟨p, hp, hxv⟩)))
  obtain ⟨p, hp, hn⟩ := (generic_decide_l O hZF hU hν).elim (fun h => False.elim (hn h)) id
  let δ : Env M 6 := (((((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z).push b).push f).push p
  let φ : BinarySchema 6 := {
    body := .existsE (.conj (below_m (.bound 8) (.bound 7) (.bound 6) .newest (.bound 3))
      (value_m (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 4) .newest (.bound 1) (.bound 2))) }
  have hφ x y : φ.denote δ x y ↔ ∃ q, Below_d M B R z q p ∧ Value_d M B R z b f q y x := by
    simp only [BinarySchema.denote, φ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      below_sat_l M hZF.1, value_sat_l M hZF.1]
    rfl
  apply ZFC.cover_bound_l I hZFC φ δ hX hW
  · intro x hx D hD
    obtain ⟨g, hg⟩ := ccc_fiber_l O hZFC hc (hU.proper p hp).1 hx hn
      (fun y => (hD y).trans (and_congr_right fun _ => hφ x y))
    obtain ⟨k, hk⟩ := hωκ
    exact ZF.exists_compositionInjection hZF I hg hk
  · intro y hy
    obtain ⟨v, hvX, hyv⟩ := hf.1.2.2 (e y) ((image_member_l e hi he).mpr hy)
    obtain ⟨x, hx, rfl⟩ := (he X v).mp hvX
    obtain ⟨q, hq, hqv⟩ := (value_truth_l O hZF hU hb e he hv hF y x).mpr hyv
    obtain ⟨r, hr, hrp, hrq⟩ := hU.directed p q hp hq
    have hr' := hU.proper r hr
    exact ⟨x, hx, (hφ x y).mpr ⟨r, ⟨hr'.1, hr'.2, hrp⟩,
      value_lower_l O b f y x q r (hU.proper q hq).1 ⟨hr'.1, hr'.2, hrq⟩ hqv⟩⟩

/-- 可数链条件反射到任意旧无限基数的基数上界。 -/
theorem ccc_cardinal_reflect_l {ω κ Y b} (hω : M.IsOmega ω) (hc : Ccc_d M I ω B R z)
    (hκ : M.IsInfiniteCardinal I ω κ) (hb : U b)
    (e : M.Domain → (E).Domain) (hi : Function.Injective e)
    (he : ∀ a y, y ∈ e a ↔ ∃ c, M.mem c a ∧ e c = y)
    (hv : ∀ a s, Check_d M b a s → Qval_d M B R z U s (e a))
    (h : (E).CardinalLessOrEqual J (e Y) (e κ)) : M.CardinalLessOrEqual I Y κ := by
  let hZF := ZFC.models_zf_l hZFC
  obtain ⟨W, hW⟩ := ZF.exists_cartesianProduct hZF I κ κ
  obtain ⟨F, hF⟩ := h
  obtain ⟨i, hiκ⟩ := ZF.exists_identityBijection hZF I κ
  obtain ⟨g, hg⟩ := ccc_injection_bound_l O hZFC hU hc hb hκ.2 ⟨i, hiκ.1⟩ hW e hi he hv hF
  obtain ⟨k, hk⟩ := ZF.cartesianSquare_cardinalLessOrEqual_of_selfMultiplication hZF I
    ⟨hκ.1, Structure.Equinumerous.refl hZF I κ⟩ hW
    (ZF.infiniteCardinal_selfMultiplication hZF I hω (ZF.omega_cardinal_l I hZF hω) hκ)
  exact ZF.exists_compositionInjection hZF I hg hk

/-- 保持每个旧无限基数；有限候选由扩张自己的 ω 基数性排除。 -/
theorem ccc_infinite_cardinal_l {ω κ b} (hω : M.IsOmega ω) (hc : Ccc_d M I ω B R z)
    (hκ : M.IsInfiniteCardinal I ω κ) (hb : U b)
    (e : M.Domain → (E).Domain) (hi : Function.Injective e)
    (he : ∀ a y, y ∈ e a ↔ ∃ c, M.mem c a ∧ e c = y)
    (hv : ∀ a s, Check_d M b a s → Qval_d M B R z U s (e a)) :
    (E).IsInfiniteCardinal J (e ω) (e κ) := by
  let hZF := ZFC.models_zf_l hZFC
  have hE := preserves_zf_l O hZF hU
  have hωE := image_omega_l (hEN := hE.1) e hi he hZF (internal_foundation_l O hZF hU) hω
    (fun T => KP.difference_exists_d (ZF.modelsKP hE) T (e ω))
  have hωc := ZF.omega_cardinal_l J hE hωE
  obtain ⟨g, hg⟩ := hκ.2
  have hgE := image_injection_l (hEN := hE.1) (hPN := KP.exists_pair (ZF.modelsKP hE)) e hi he hg
  refine ⟨⟨image_ordinal_l e hi he hZF.1 (internal_foundation_l O hZF hU) hκ.1.1, ?_⟩, ⟨e g, hgE⟩⟩
  intro β hβ hβκ
  obtain ⟨α, hακ, rfl⟩ := (he κ β).mp hβ
  obtain ⟨μ, hμ, _⟩ := ZF.ordinalCardinal_existsUnique hZF I (hκ.1.1.mem hακ)
  obtain ⟨f, hf⟩ := hβκ.symm hE J
  obtain ⟨j, hj⟩ := hμ.2.symm hZF I
  have hjE := image_injection_l (hEN := hE.1) (hPN := KP.exists_pair (ZF.modelsKP hE)) e hi he hj.1
  have hκμE := ZF.exists_compositionInjection hE J hf.1 hjE
  classical
  by_cases hωμ : M.CardinalLessOrEqual I ω μ
  · obtain ⟨r, hr⟩ := ccc_cardinal_reflect_l O hZFC hU hω hc ⟨hμ.1, hωμ⟩ hb e hi he hv hκμE
    obtain ⟨s, hs⟩ := hμ.2
    have hκα := ZF.exists_compositionInjection hZF I hr hs.1
    have hακ' := ZF.exists_inclusionInjection hZF I (hκ.1.1.transitive α hακ)
    exact hκ.1.2 α hακ (ZF.equinumerous_of_cardinalLessOrEqual hZF I hακ' hκα)
  · have hμω : M.mem μ ω := by
      rcases hμ.1.1.trichotomy hZF.1 (hω.isOrdinal hZF) (KP.difference_exists_d (ZF.modelsKP hZF))
          (KP.intersection_exists_d (ZF.modelsKP hZF) μ ω) with heq | hμω | hωμ'
      · have heq := hZF.1.eq_of_same_members μ ω heq
        exact False.elim (hωμ (heq.symm ▸ ZF.exists_inclusionInjection hZF I (fun _ h => h)))
      · exact hμω
      · exact False.elim (hωμ (ZF.exists_inclusionInjection hZF I (hμ.1.1.transitive ω hωμ')))
    obtain ⟨r, hr⟩ := hκμE
    have hωμE := ZF.exists_compositionInjection hE J hgE hr
    have hμωE := (image_member_l e hi he).mpr hμω
    have hμω' := ZF.exists_inclusionInjection hE J ((hωE.isOrdinal hE).transitive (e μ) hμωE)
    exact hωc.2 (e μ) hμωE (ZF.equinumerous_of_cardinalLessOrEqual hE J hμω' hωμE)

end YesMetaZFC.Model.Forcing.Internal
