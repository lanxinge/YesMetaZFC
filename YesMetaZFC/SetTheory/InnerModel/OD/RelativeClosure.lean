import YesMetaZFC.SetTheory.InnerModel.OD.Relative

/-! # 两种参数域的共同细化与有限定义闭性 -/
namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

theorem oa_common_l (hZF : M.Models ZF) (k : Bool) {A p q : M.Domain}
    (hp : Oa_param_d k A p) (hq : Oa_param_d k A q) :
    ∃ r, Oa_param_d k A r ∧ Ob_d r p ∧ Ob_d r q := by
  cases k with
  | false =>
    change p = A at hp; change q = A at hq
    subst p q
    exact ⟨A, rfl, ob_parameter_l hZF A, ob_parameter_l hZF A⟩
  | true =>
    obtain ⟨s, hs, hp⟩ := hp
    obtain ⟨t, ht, hq⟩ := hq
    obtain ⟨ω, hω⟩ := ZF.exists_omega hZF
    let I := kp_pair_l (ZF.modelsKP hZF)
    obtain ⟨n, hn, hs⟩ := (oa_seq_decode_l hZF hω).mp hs
    obtain ⟨m, hm, ht⟩ := (oa_seq_decode_l hZF hω).mp ht
    obtain ⟨l, F, hl, hF, hS, hT⟩ := ZF.fseq_join_l I hZF hω hn hm hs ht
    obtain ⟨r, hr⟩ := I.total A F
    obtain ⟨ha, hf⟩ := ob_pair_components_l hZF r (ob_parameter_l hZF r) hr
    have hno := ob_ordinal_l hZF r (hω.members_areOrdinals hZF n hn)
    have hmo := ob_ordinal_l hZF r (hω.members_areOrdinals hZF m hm)
    have hso : Ob_d r s := by
      let φ : UnarySchema 2 := { body := Formula.isRestriction kpair_convention_l .newest (.bound 1) (.bound 2) }
      let ρ : Env M 2 := ⟨Fin.cases F (fun _ => n), fun _ => F⟩
      exact ob_closed_l hZF r φ ρ (Fin.cases hf (fun _ => hno)) (fun g =>
        (Formula.satisfies_isRestriction_iff I _ _ _ _).trans
          ⟨fun hg => hg.eq hZF.1 hS, fun he => he.symm ▸ hS⟩)
    have hto : Ob_d r t := by
      let φ : UnarySchema 3 := { body := fs_tail_m (𝒞 := kpair_convention_l) (.bound 2) (.bound 3) (.bound 1) .newest }
      let ρ : Env M 3 := ⟨Fin.cases F (Fin.cases n (fun _ => m)), fun _ => F⟩
      exact ob_closed_l hZF r φ ρ (Fin.cases hf (Fin.cases hno (fun _ => hmo))) (fun g =>
        (fs_tail_sat_l I hZF.1 _ _ _ _ _).trans
          ⟨fun hg => fs_tail_unique_l I hZF.1 hg hT, fun he => he.symm ▸ hT⟩)
    exact ⟨r, ⟨F, (oa_seq_decode_l hZF hω).mpr ⟨l, hl, hF⟩, hr⟩,
      ob_pair_l hZF r ha hso hp, ob_pair_l hZF r ha hto hq⟩

theorem oa_finite_l (hZF : M.Models ZF) (k : Bool) (A : M.Domain) {n} (v : Fin n → M.Domain)
    (hv : ∀ i, Oa_d k A (v i)) : ∃ p, Oa_param_d k A p ∧ ∀ i, Ob_d p (v i) := by
  induction n with
  | zero =>
    obtain ⟨p, hp, _⟩ := oa_seed_l hZF k A
    exact ⟨p, hp, fun i => Fin.elim0 i⟩
  | succ n ih =>
    obtain ⟨p, hp, h0⟩ := hv 0
    obtain ⟨q, hq, h⟩ := ih (fun i => v i.succ) (fun i => hv i.succ)
    obtain ⟨r, hr, hrp, hrq⟩ := oa_common_l hZF k hp hq
    exact ⟨r, hr, Fin.cases (ob_trans_l hZF hrp h0) (fun i => ob_trans_l hZF hrq (h i))⟩

theorem oa_unique_l (hZF : M.Models ZF) (k : Bool) (A : M.Domain) {n} (φ : UnarySchema n)
    (ρ : Env M n) (hρ : ∀ i, Oa_d k A (ρ.bound i)) {x} (hx : ∀ y, φ.denote ρ y ↔ y = x) : Oa_d k A x := by
  obtain ⟨p, hp, h⟩ := oa_finite_l hZF k A ρ.bound hρ
  exact ⟨p, hp, ob_closed_l hZF p φ ρ h hx⟩

theorem oa_parameter_l (hZF : M.Models ZF) (k : Bool) (A : M.Domain) : Oa_d k A A :=
  oa_of_ob_l hZF k (ob_parameter_l hZF A)

theorem oa_ordinal_l (hZF : M.Models ZF) (k : Bool) (A : M.Domain) {x} (hx : M.IsOrdinal x) : Oa_d k A x :=
  oa_of_ob_l hZF k (ob_ordinal_l hZF A hx)

/-- A 的每个成员都能作为圆括号参数：用实际单项序列保存它。 -/
theorem op_member_l (hZF : M.Models ZF) {A a : M.Domain} (ha : M.mem a A) : Op_d A a := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨ω, hω⟩ := ZF.exists_omega hZF
  obtain ⟨e, he, heω⟩ := hω.1.1
  obtain ⟨n, hn, hnω⟩ := hω.1.2 e heω
  obtain ⟨f, hf, hF⟩ := ZF.exists_constantFunction hZF I (source := n) ha
  obtain ⟨p, hp⟩ := I.total A f
  have hfO := (ob_pair_components_l hZF p (ob_parameter_l hZF p) hp).2
  let φ : UnarySchema 2 := { body := Formula.orderedPairMem kpair_convention_l (.bound 2) .newest (.bound 1) }
  let ρ : Env M 2 := ⟨Fin.cases f (fun _ => e), fun _ => f⟩
  have hfa := (hF e a).mpr ⟨hn.predecessor_mem, rfl⟩
  have ho : Ob_d p a := ob_closed_l hZF p φ ρ
    (Fin.cases hfO (fun _ => ob_ordinal_l hZF p (Structure.IsOrdinal.of_no_members he)))
    (fun y => (Formula.satisfies_orderedPairMem_iff I _ _ _ _).trans
      ⟨fun hy => hf.1.2 e y a hy hfa, fun hy => hy.symm ▸ hfa⟩)
  exact ⟨p, ⟨f, (oa_seq_decode_l hZF hω).mpr ⟨n, hnω, hf⟩, hp⟩, ho⟩

end YesMetaZFC.SetTheory.InnerModel
