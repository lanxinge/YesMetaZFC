import YesMetaZFC.Model.Forcing.Stage.Embedding

/-! # 阶段完全嵌入的内部复合

复合关系在地模型中分离为集合图，约减沿两次嵌入合成。整个过程保留正条件、
序反射和相容性，不对源集或模型提出外部可数性要求。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {P R z Q S w T V v F G : M.Domain}

/-- 正条件上的恒等图给出阶段系统的实际起始嵌入。 -/
theorem reg_embed_id_l (hZF : M.Models ZF) (O : Cond_order_d M P R z) :
    ∃ F, (∀ p x, Entry_d M p x F ↔ M.mem p P ∧ p ≠ z ∧ x = p) ∧
      Reg_embed_d M P R z P R z F := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  let ρ : Env M 1 := ⟨fun _ => z, fun _ => z⟩
  let φ : BinarySchema 1 := {
    body := .conj (Formula.extensionalEq .newest (.bound 1))
      (.neg (Formula.extensionalEq (.bound 1) (.bound 2))) }
  have hφ p x : φ.denote ρ p x ↔ x = p ∧ p ≠ z := by
    simp only [BinarySchema.denote, φ, Formula.satisfies_conj_iff, Formula.satisfies_neg_iff,
      Formula.satisfies_extensionalEq_iff_eq hZF.1]
    rfl
  obtain ⟨F, hGraph, hf⟩ := ZF.exists_setRelationOn_of_denote hZF I φ ρ P
  have hF p x : Entry_d M p x F ↔ M.mem p P ∧ p ≠ z ∧ x = p := by
    refine (hf p x).trans ?_
    rw [hφ]
    exact ⟨fun ⟨hp, _, he, hz⟩ => ⟨hp, hz, he⟩,
      fun ⟨hp, hz, he⟩ => ⟨hp, he.symm ▸ hp, he, hz⟩⟩
  refine ⟨F, hF, {
    graph := hGraph.1
    total := fun p hp hz => ⟨p, (hF p p).mpr ⟨hp, hz, rfl⟩⟩
    domain := ?_, functional := ?_, injective := ?_, order := ?_, compat := ?_, reduction := ?_ }⟩
  · intro p x hpx
    obtain ⟨hp, hz, rfl⟩ := (hF p x).mp hpx
    exact ⟨hp, hz, hp, hz⟩
  · intro p x y hx hy
    exact ((hF p x).mp hx).2.2.trans ((hF p y).mp hy).2.2.symm
  · intro p q x hp hq
    exact ((hF p x).mp hp).2.2.symm.trans ((hF q x).mp hq).2.2
  · intro p q x y hp hq
    rw [((hF p x).mp hp).2.2, ((hF q y).mp hq).2.2]
  · intro p q x y hp hq
    rw [((hF p x).mp hp).2.2, ((hF q y).mp hq).2.2]
  · intro x hx hz
    refine ⟨x, hx, hz, fun q y hqy hqx => ?_⟩
    obtain ⟨hq, hqz, rfl⟩ := (hF q y).mp hqy
    exact ⟨y, ⟨hq, hqz, hqx⟩, O.refl y hq⟩

/-- 完全嵌入实际复合为地模型内的图，并保留目标条件约减。 -/
theorem reg_embed_comp_l (hZF : M.Models ZF) (L : Cond_order_d M T V v)
    (h : Reg_embed_d M P R z Q S w F) (k : Reg_embed_d M Q S w T V v G) :
    ∃ H, (∀ p x, Entry_d M p x H ↔ ∃ q, Entry_d M p q F ∧ Entry_d M q x G) ∧
      Reg_embed_d M P R z T V v H := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  let ρ : Env M 2 := (⟨fun _ => F, fun _ => F⟩ : Env M 1).push G
  let φ : BinarySchema 2 := {
    body := .existsE (.conj (entry_m (.bound 2) .newest (.bound 4))
      (entry_m .newest (.bound 1) (.bound 3))) }
  have hφ p x : φ.denote ρ p x ↔ ∃ q, Entry_d M p q F ∧ Entry_d M q x G := by
    simp only [BinarySchema.denote, φ, Formula.satisfies_exists_iff,
      Formula.satisfies_conj_iff, entry_sat_l M hZF.1]
    rfl
  obtain ⟨A, hA⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) P T
  obtain ⟨H, hGraph, hH'⟩ := ZF.exists_setRelationOn_of_denote hZF I φ ρ A
  have hH p x : Entry_d M p x H ↔ ∃ q, Entry_d M p q F ∧ Entry_d M q x G := by
    refine (hH' p x).trans ?_
    rw [hφ]
    exact ⟨fun h => h.2.2, fun ⟨q, hpq, hqx⟩ =>
      ⟨(hA p).mpr (Or.inl (h.domain p q hpq).1),
        (hA x).mpr (Or.inr (k.domain q x hqx).2.2.1), q, hpq, hqx⟩⟩
  refine ⟨H, hH, {
    graph := hGraph.1, total := ?_, domain := ?_, functional := ?_, injective := ?_,
    order := ?_, compat := ?_, reduction := ?_ }⟩
  · intro p hp hz
    obtain ⟨q, hpq⟩ := h.total p hp hz
    obtain ⟨x, hqx⟩ := k.total q (h.domain p q hpq).2.2.1 (h.domain p q hpq).2.2.2
    exact ⟨x, (hH p x).mpr ⟨q, hpq, hqx⟩⟩
  · intro p x hpx
    obtain ⟨q, hpq, hqx⟩ := (hH p x).mp hpx
    exact ⟨(h.domain p q hpq).1, (h.domain p q hpq).2.1, (k.domain q x hqx).2.2⟩
  · intro p x y hpx hpy
    obtain ⟨q, hpq, hqx⟩ := (hH p x).mp hpx
    obtain ⟨r, hpr, hry⟩ := (hH p y).mp hpy
    have he := h.functional p q r hpq hpr
    subst r
    exact k.functional q x y hqx hry
  · intro p r x hpx hrx
    obtain ⟨q, hpq, hqx⟩ := (hH p x).mp hpx
    obtain ⟨s, hrs, hsx⟩ := (hH r x).mp hrx
    have he := k.injective q s x hqx hsx
    subst s
    exact h.injective p r q hpq hrs
  · intro p r x y hpx hry
    obtain ⟨q, hpq, hqx⟩ := (hH p x).mp hpx
    obtain ⟨s, hrs, hsy⟩ := (hH r y).mp hry
    exact (k.order q s x y hqx hsy).trans (h.order p r q s hpq hrs)
  · intro p r x y hpx hry
    obtain ⟨q, hpq, hqx⟩ := (hH p x).mp hpx
    obtain ⟨s, hrs, hsy⟩ := (hH r y).mp hry
    exact (k.compat q s x y hqx hsy).trans (h.compat p r q s hpq hrs)
  · intro x hx hxv
    obtain ⟨q, hq, hqw, hqx⟩ := k.reduction x hx hxv
    obtain ⟨p, hp, hpz, hpq⟩ := h.reduction q hq hqw
    refine ⟨p, hp, hpz, fun r y hry hrp => ?_⟩
    obtain ⟨s, hrs, hsy⟩ := (hH r y).mp hry
    obtain ⟨a, haq, has⟩ := hpq r s hrs hrp
    obtain ⟨c, hac⟩ := k.total a haq.1 haq.2.1
    obtain ⟨d, hdx, hdc⟩ := hqx a c hac haq.2.2
    exact ⟨d, hdx, L.trans d c y hdx.1 (k.domain a c hac).2.2.1
      (k.domain s y hsy).2.2.1 hdc ((k.order a s c y hac hsy).mpr has)⟩

end YesMetaZFC.Model.Forcing.Internal
