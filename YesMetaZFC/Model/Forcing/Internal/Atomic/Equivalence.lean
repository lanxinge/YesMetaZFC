import YesMetaZFC.Model.Forcing.Internal.Forcing.Conditions

/-! # 任意地模型中的原子力迫等价与替换

在模型内三元组集合上分离对角、逆关系与复合关系，直接构造双模拟证书。
中间名称可遍历模型，只有证书的两个端点需要固定闭支撑；全程不使用外部良基性。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain}

/-- 两次有序对分离把实际三元公式实现为模型内的有界关系。 -/
theorem rel_separation_bound_l (hZF : M.Models ZF) {n} (φ : BinarySchema (n + 1))
    (ρ : Env M n) (B S : M.Domain) : ∃ F,
      (∀ v, M.mem v F → ∃ p s t, M.mem p B ∧ M.mem s S ∧ M.mem t S ∧ Triple_d M v p s t) ∧
      ∀ p s t, Rel_d M F p s t ↔
      M.mem p B ∧ M.mem s S ∧ M.mem t S ∧ φ.denote (ρ.push p) s t := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  let χ : BinarySchema n := ⟨(UnarySchema.relationMember kpair_convention_l φ).body,
    (UnarySchema.relationMember kpair_convention_l φ).freeClosed⟩
  obtain ⟨X, hX⟩ := triple_carrier_l M hZF B S
  obtain ⟨F, hF⟩ := ZF.separation_exists_d hZF (UnarySchema.relationMember kpair_convention_l χ) ρ X
  have hc p a : χ.denote ρ p a ↔ ∃ s t, KPair_d M a s t ∧ φ.denote (ρ.push p) s t :=
    Formula.satisfies_relationMember_iff I φ (ρ.push p) a
  refine ⟨F, (fun v hv => (hX v).mp ((hF v).mp hv).1), fun p s t => ?_⟩
  constructor
  · rintro ⟨q, hq, hqF⟩
    obtain ⟨hqX, hqφ⟩ := (hF q).mp hqF
    obtain ⟨p', s', t', hp, hs, ht, hq'⟩ := (hX q).mp hqX
    obtain ⟨rfl, rfl, rfl⟩ := triple_inj_l M hq hq'
    obtain ⟨p', a, hqa, ha⟩ := (Formula.satisfies_relationMember_iff I χ ρ q).mp hqφ
    obtain ⟨s', t', ha, hφ⟩ := (hc p' a).mp ha
    obtain ⟨rfl, rfl, rfl⟩ := triple_inj_l M hq ⟨a, ha, hqa⟩
    exact ⟨hp, hs, ht, hφ⟩
  · rintro ⟨hp, hs, ht, hφ⟩
    obtain ⟨q, a, ha, hq⟩ := triple_exists_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) p s t
    refine ⟨q, ⟨a, ha, hq⟩, (hF q).mpr ⟨(hX q).mpr ⟨p, s, t, hp, hs, ht, a, ha, hq⟩, ?_⟩⟩
    exact (Formula.satisfies_relationMember_iff I χ ρ q).mpr ⟨p, a, hq, (hc p a).mpr ⟨s, t, ha, hφ⟩⟩

/-- 不需要显式载体界时，直接读取同一分离图的条目方程。 -/
theorem rel_separation_l (hZF : M.Models ZF) {n} (φ : BinarySchema (n + 1))
    (ρ : Env M n) (B S : M.Domain) : ∃ F, ∀ p s t, Rel_d M F p s t ↔
      M.mem p B ∧ M.mem s S ∧ M.mem t S ∧ φ.denote (ρ.push p) s t := by
  obtain ⟨F, _, hF⟩ := rel_separation_bound_l hZF φ ρ B S
  exact ⟨F, hF⟩

variable (O : Cond_order_d M B R z) (hZF : M.Models ZF)
include O hZF

/-- 对角关系在闭支撑内形成双模拟。 -/
theorem eq_force_refl_l {p s} (hp : M.mem p B) (hs : Name_d M B s) :
    Eq_force_d M B R z p s s := by
  obtain ⟨S, hs, hS⟩ := hs
  let φ : BinarySchema 1 := { body := Formula.extensionalEq (.bound 1) (.bound 0) }
  obtain ⟨F, hF⟩ := rel_separation_l hZF φ (⟨(fun i => nomatch i), fun _ => p⟩ : Env M 0) B S
  have he a b c : Rel_d M F a b c ↔ M.mem a B ∧ M.mem b S ∧ M.mem c S ∧ b = c := by
    simpa only [BinarySchema.denote, φ, Formula.satisfies_extensionalEq_iff_eq hZF.1] using! hF a b c
  refine ⟨hp, F, ?_, (he p s s).mpr ⟨hp, hs, hs, rfl⟩⟩
  intro p s t h
  obtain ⟨_, hs, _, rfl⟩ := (he p s t).mp h
  have hm (k : Bool) : Match_d M k B R z F p s s := by
    intro a b hab q hq hqb
    have ha := (supp_entry_l M hS hs hab).1
    refine ⟨q, a, b, below_refl_l O hq.1 hq.2.1, hab, hqb, ?_⟩
    cases k <;> exact (he q a a).mpr ⟨hq.1, ha, ha, rfl⟩
  exact ⟨hm false, hm true⟩

omit O in
/-- 交换关系的两个名称端点，同时交换双向匹配。 -/
theorem eq_force_symm_l {p s t} (hs : Name_d M B s) (ht : Name_d M B t)
    (h : Eq_force_d M B R z p s t) : Eq_force_d M B R z p t s := by
  obtain ⟨S, hsS, htS, hS⟩ := name_support_l M (KP.exists_pair (ZF.modelsKP hZF))
    (KP.exists_union (ZF.modelsKP hZF)) hs ht
  let ρ : Env M 3 := ((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z
  let φ : BinarySchema 4 := {
    body := eq_force_m (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 0) (.bound 1) }
  obtain ⟨F, hF⟩ := rel_separation_l hZF φ ρ B S
  have he p s t : Rel_d M F p s t ↔
      M.mem p B ∧ M.mem s S ∧ M.mem t S ∧ Eq_force_d M B R z p t s := by
    simpa only [BinarySchema.denote, φ, eq_force_sat_l M hZF.1] using! hF p s t
  refine ⟨h.1, F, ?_, (he p t s).mpr ⟨h.1, htS, hsS, h⟩⟩
  intro p s t h
  obtain ⟨_, hs, ht, h⟩ := (he p s t).mp h
  obtain ⟨_, hl, hr⟩ := (eq_force_unfold_l M hZF ⟨S, ht, hS⟩ ⟨S, hs, hS⟩).mp h
  constructor
  · intro a b hab q hq hqb
    obtain ⟨r, d, c, hr, hd, hrc, heq⟩ := hr a b hab q hq hqb
    exact ⟨r, d, c, hr, hd, hrc, (he r a d).mpr
      ⟨hr.1, (supp_entry_l M hS hs hab).1, (supp_entry_l M hS ht hd).1, heq⟩⟩
  · intro a b hab q hq hqb
    obtain ⟨r, d, c, hr, hd, hrc, heq⟩ := hl a b hab q hq hqb
    exact ⟨r, d, c, hr, hd, hrc, (he r d a).mpr
      ⟨hr.1, (supp_entry_l M hS hs hd).1, (supp_entry_l M hS ht hab).1, heq⟩⟩

/-- 复合双模拟逐次加强条件；中间名称不需要外部秩。 -/
theorem eq_force_trans_l {p s t v} (hs : Name_d M B s) (ht : Name_d M B t)
    (hv : Name_d M B v) (h : Eq_force_d M B R z p s t) (k : Eq_force_d M B R z p t v) :
    Eq_force_d M B R z p s v := by
  obtain ⟨S, hsS, hvS, hS⟩ := name_support_l M (KP.exists_pair (ZF.modelsKP hZF))
    (KP.exists_union (ZF.modelsKP hZF)) hs hv
  let ρ : Env M 3 := ((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z
  let φ : BinarySchema 4 := {
    body := .existsE (.conj (name_m (.bound 6) .newest)
      (.conj (eq_force_m (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) .newest)
        (eq_force_m (.bound 6) (.bound 5) (.bound 4) (.bound 3) .newest (.bound 1)))) }
  obtain ⟨F, hF⟩ := rel_separation_l hZF φ ρ B S
  have he p s v : Rel_d M F p s v ↔ M.mem p B ∧ M.mem s S ∧ M.mem v S ∧
      ∃ t, Name_d M B t ∧ Eq_force_d M B R z p s t ∧ Eq_force_d M B R z p t v := by
    simpa only [BinarySchema.denote, φ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      name_sat_l M hZF.1, eq_force_sat_l M hZF.1] using! hF p s v
  refine ⟨h.1, F, ?_, (he p s v).mpr ⟨h.1, hsS, hvS, t, ht, h, k⟩⟩
  intro p s v h
  obtain ⟨_, hs, hv, t, ht, h, k⟩ := (he p s v).mp h
  have hsN : Name_d M B s := ⟨S, hs, hS⟩
  have hvN : Name_d M B v := ⟨S, hv, hS⟩
  obtain ⟨hp, hl, hback⟩ := (eq_force_unfold_l M hZF hsN ht).mp h
  obtain ⟨_, kl, kr⟩ := (eq_force_unfold_l M hZF ht hvN).mp k
  constructor
  · intro a b hab q hq hqb
    obtain ⟨r, d, c, hr, hd, hrc, had⟩ := hl a b hab q hq hqb
    obtain ⟨w, e, f, hw, he', hwf, hde⟩ := kl d c hd r (below_trans_l O hp hr hq) hrc
    have haN := (name_entry_l M hsN hab).1
    have hdN := (name_entry_l M ht hd).1
    exact ⟨w, e, f, below_trans_l O hq.1 hw hr, he', hwf, (he w a e).mpr
      ⟨hw.1, (supp_entry_l M hS hs hab).1, (supp_entry_l M hS hv he').1, d, hdN,
        eq_force_lower_l O hZF haN hdN r w hr.1 hw had, hde⟩⟩
  · intro a b hab q hq hqb
    obtain ⟨r, d, c, hr, hd, hrc, hda⟩ := kr a b hab q hq hqb
    obtain ⟨w, e, f, hw, he', hwf, hed⟩ := hback d c hd r (below_trans_l O hp hr hq) hrc
    have haN := (name_entry_l M hvN hab).1
    have hdN := (name_entry_l M ht hd).1
    exact ⟨w, e, f, below_trans_l O hq.1 hw hr, he', hwf, (he w e a).mpr
      ⟨hw.1, (supp_entry_l M hS hs he').1, (supp_entry_l M hS hv hab).1, d, hdN, hed,
        eq_force_lower_l O hZF hdN haN r w hr.1 hw hda⟩⟩

/-- 等同名称可替换隶属式的左项。 -/
theorem mem_force_left_l {p s t v} (hs : Name_d M B s) (ht : Name_d M B t)
    (hv : Name_d M B v) (h : Eq_force_d M B R z p s t) (k : Mem_force_d M B R z p s v) :
    Mem_force_d M B R z p t v := by
  refine ⟨k.1, fun q hq => ?_⟩
  obtain ⟨r, a, b, hr, ha, hrb, he⟩ := k.2 q hq
  have h' := eq_force_lower_l O hZF hs ht p r h.1 (below_trans_l O h.1 hr hq) h
  exact ⟨r, a, b, hr, ha, hrb, eq_force_trans_l O hZF ht hs (name_entry_l M hv ha).1
    (eq_force_symm_l hZF hs ht h') he⟩

/-- 等同名称可替换隶属式的右项。 -/
theorem mem_force_right_l {p s t v} (hs : Name_d M B s) (ht : Name_d M B t)
    (hv : Name_d M B v) (h : Eq_force_d M B R z p t v) (k : Mem_force_d M B R z p s t) :
    Mem_force_d M B R z p s v := by
  obtain ⟨hp, hl, _⟩ := (eq_force_unfold_l M hZF ht hv).mp h
  refine ⟨hp, fun q hq => ?_⟩
  obtain ⟨r, a, b, hr, ha, hrb, he⟩ := k.2 q hq
  obtain ⟨w, d, c, hw, hd, hwc, had⟩ := hl a b ha r (below_trans_l O hp hr hq) hrb
  have haN := (name_entry_l M ht ha).1
  exact ⟨w, d, c, below_trans_l O hq.1 hw hr, hd, hwc,
    eq_force_trans_l O hZF hs haN (name_entry_l M hv hd).1
      (eq_force_lower_l O hZF hs haN r w hr.1 hw he) had⟩

/-- 一个名称条目在其系数以下直接力迫隶属。 -/
theorem mem_force_entry_l {p s t b} (hp : M.mem p B) (hs : Name_d M B s)
    (hb : M.mem b B) (h : Entry_d M s b t) (hpb : Entry_d M p b R) :
    Mem_force_d M B R z p s t :=
  ⟨hp, fun q hq => ⟨q, s, b, below_refl_l O hq.1 hq.2.1, h,
    O.trans q p b hq.1 hp hb hq.2.2 hpb, eq_force_refl_l O hZF hq.1 hs⟩⟩

end YesMetaZFC.Model.Forcing.Internal
