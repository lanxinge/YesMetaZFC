import YesMetaZFC.Model.Forcing.Stage.Embedding

/-! # 内部偏序的可定义重编码

沿模型中的实际集合双射搬运条件序，同时构造目标关系图、序反射、相容性和
约减证书。条件集自身作为排除值，适用于二步及支撑迭代的后继条件重编码。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {P R Q F : M.Domain}

theorem order_transport_l (hZF : M.Models ZF) (O : Cond_order_d M P R P)
    (hF : M.IsSetBijectionFromTo (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) F P Q) :
    ∃ S, (∀ v, M.mem v S → ∃ x y, KPair_d M v x y) ∧
      (∀ x y, Entry_d M x y S ↔ ∃ p q, Entry_d M p x F ∧ Entry_d M q y F ∧ Entry_d M p q R) ∧
      Cond_order_d M Q S Q ∧ Reg_embed_d M P R P Q S Q F := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  have src {p x} (hp : Entry_d M p x F) : M.mem p P := hF.1.1.input_mem_of_pairMember hp
  have tgt {p x} (hp : Entry_d M p x F) : M.mem x Q := hF.1.1.output_mem_of_pairMember hp
  have pn {p} (hp : M.mem p P) : p ≠ P := fun he => KP.mem_irrefl_d (ZF.modelsKP hZF) P (he ▸ hp)
  have qn {q} (hq : M.mem q Q) : q ≠ Q := fun he => KP.mem_irrefl_d (ZF.modelsKP hZF) Q (he ▸ hq)
  let ρ : Env M 2 := (⟨fun _ => R, fun _ => R⟩ : Env M 1).push F
  let φ : BinarySchema 2 := {
    body := .existsE (.existsE (.conj (entry_m (.bound 1) (.bound 3) (.bound 4))
      (.conj (entry_m .newest (.bound 2) (.bound 4)) (entry_m (.bound 1) .newest (.bound 5))))) }
  have hφ x y : φ.denote ρ x y ↔ ∃ p q, Entry_d M p x F ∧ Entry_d M q y F ∧ Entry_d M p q R := by
    simp only [BinarySchema.denote, φ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, entry_sat_l M hZF.1]
    rfl
  obtain ⟨S, hGraph, hS⟩ := ZF.exists_setRelationOn_of_denote hZF I φ ρ Q
  have hs x y : Entry_d M x y S ↔ ∃ p q, Entry_d M p x F ∧ Entry_d M q y F ∧ Entry_d M p q R := by
    refine (hS x y).trans ?_
    rw [hφ]
    exact ⟨fun hh => hh.2.2, fun ⟨p, q, hpx, hqy, hpq⟩ => ⟨tgt hpx, tgt hqy, p, q, hpx, hqy, hpq⟩⟩
  have ord {p q x y} (hpx : Entry_d M p x F) (hqy : Entry_d M q y F) :
      Entry_d M x y S ↔ Entry_d M p q R := by
    refine (hs x y).trans ⟨?_, fun hpq => ⟨p, q, hpx, hqy, hpq⟩⟩
    rintro ⟨a, b, hax, hby, hab⟩
    have ha := hF.1.2 a p x hax hpx
    have hb := hF.1.2 b q y hby hqy
    exact ha ▸ hb ▸ hab
  have L : Cond_order_d M Q S Q := by
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨p, hp, hpx⟩ := hF.2 x hx
      exact (ord hpx hpx).mpr (O.refl p hp)
    · intro x y z _ _ _ hxy hyz
      obtain ⟨p, q, hpx, hqy, hpq⟩ := (hs x y).mp hxy
      obtain ⟨q', r, hq'y, hrz, hq'r⟩ := (hs y z).mp hyz
      have he := hF.1.2 q' q y hq'y hqy
      subst q'
      exact (ord hpx hrz).mpr (O.trans p q r (src hpx) (src hqy) (src hrz) hpq hq'r)
    · intro x _ hx
      obtain ⟨p, q, _, hq, _⟩ := (hs x Q).mp hx
      exact False.elim (KP.mem_irrefl_d (ZF.modelsKP hZF) Q (tgt hq))
  have cmp {p q x y} (hpx : Entry_d M p x F) (hqy : Entry_d M q y F) :
      Cmp_d M Q S Q x y ↔ Cmp_d M P R P p q := by
    constructor
    · rintro ⟨z, hzx, hzy⟩
      obtain ⟨r, hr, hrz⟩ := hF.2 z hzx.1
      exact ⟨r, ⟨hr, pn hr, (ord hrz hpx).mp hzx.2.2⟩, (ord hrz hqy).mp hzy⟩
    · rintro ⟨r, hrp, hrq⟩
      obtain ⟨z, hz, hrz⟩ := hF.1.1.2.2 r hrp.1
      exact ⟨z, ⟨hz, qn hz, (ord hrz hpx).mpr hrp.2.2⟩, (ord hrz hqy).mpr hrq⟩
  refine ⟨S, hGraph.1, hs, L, {
    graph := hF.1.1.1.1
    total := fun p hp _ => (hF.1.1.2.2 p hp).elim (fun x hx => ⟨x, hx.2⟩)
    domain := fun p x hpx => ⟨src hpx, pn (src hpx), tgt hpx, qn (tgt hpx)⟩
    functional := hF.1.1.1.2
    injective := hF.1.2
    order := fun _ _ _ _ hp hq => ord hp hq
    compat := fun _ _ _ _ hp hq => cmp hp hq
    reduction := ?_ }⟩
  intro x hx _
  obtain ⟨p, hp, hpx⟩ := hF.2 x hx
  exact ⟨p, hp, pn hp, fun q y hqy hqp =>
    ⟨y, ⟨tgt hqy, qn (tgt hqy), (ord hqy hpx).mpr hqp⟩, L.refl y (tgt hqy)⟩⟩

/-- 对给定实际原公式的单射重编码，一次构造像集、双射图及搬运后的偏序。 -/
theorem order_recode_l (hZF : M.Models ZF) (O : Cond_order_d M P R P) {n}
    (φ : BinarySchema n) (ρ : Env M n)
    (ht : ∀ p, M.mem p P → ∃ x, φ.denote ρ p x)
    (hf : ∀ p, M.mem p P → ∀ x y, φ.denote ρ p x → φ.denote ρ p y → x = y)
    (hi : ∀ p q x, M.mem p P → M.mem q P → φ.denote ρ p x → φ.denote ρ q x → p = q) :
    ∃ Q S F, (∀ x, M.mem x Q ↔ ∃ p, M.mem p P ∧ φ.denote ρ p x) ∧
      (∀ p x, Entry_d M p x F ↔ M.mem p P ∧ φ.denote ρ p x) ∧
      M.IsSetBijectionFromTo (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) F P Q ∧
      (∀ v, M.mem v S → ∃ x y, KPair_d M v x y) ∧
      (∀ x y, Entry_d M x y S ↔ ∃ p q, Entry_d M p x F ∧ Entry_d M q y F ∧ Entry_d M p q R) ∧
      Cond_order_d M Q S Q ∧ Reg_embed_d M P R P Q S Q F := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨Q, hQ⟩ := ZF.exists_functionalImageOn hZF φ ρ P ht hf
  obtain ⟨F, hFn, hF⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ ht hf
    (fun p x hp hx => (hQ x).mpr ⟨p, hp, hx⟩)
  have hb : M.IsSetBijectionFromTo I F P Q := by
    refine ⟨⟨hFn, fun p q x hpx hqx => ?_⟩, fun x hx => ?_⟩
    · exact hi p q x ((hF p x).mp hpx).1 ((hF q x).mp hqx).1 ((hF p x).mp hpx).2 ((hF q x).mp hqx).2
    · obtain ⟨p, hp, hpx⟩ := (hQ x).mp hx
      exact ⟨p, hp, (hF p x).mpr ⟨hp, hpx⟩⟩
  obtain ⟨S, hGraph, hS, L, h⟩ := order_transport_l hZF O hb
  exact ⟨Q, S, F, hQ, hF, hb, hGraph, hS, L, h⟩

end YesMetaZFC.Model.Forcing.Internal
