import YesMetaZFC.Model.Forcing.Internal.Automorphism.Names

/-! # 条件自同构保持原子力迫

在目标名称的闭支撑上分离源等号关系的像，得到实际集合双模拟。任意目标加强
由逆条件拉回，再把源匹配送到目标。此论证只需双射保序，不额外消费预序公理。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}}

private def Aut_eq_d (B R z F q s t : M.Domain) : Prop := ∃ p x y,
  Entry_d M p q F ∧ Name_d M B x ∧ Name_d M B y ∧
    Nmap_d M F x s ∧ Nmap_d M F y t ∧ Eq_force_d M B R z p x y

private def aut_eq_m {n} (B R z F q s t : Term n) : Formula 1 n :=
  .existsE <| .existsE <| .existsE <|
    .conj (entry_m (.bound 2) q.weaken.weaken.weaken F.weaken.weaken.weaken) <|
    .conj (name_m B.weaken.weaken.weaken (.bound 1)) <|
    .conj (name_m B.weaken.weaken.weaken .newest) <|
    .conj (nmap_m F.weaken.weaken.weaken (.bound 1) s.weaken.weaken.weaken) <|
    .conj (nmap_m F.weaken.weaken.weaken .newest t.weaken.weaken.weaken)
      (eq_force_m B.weaken.weaken.weaken R.weaken.weaken.weaken z.weaken.weaken.weaken
        (.bound 2) (.bound 1) .newest)
derive_free_closed aut_eq_m

private theorem aut_eq_sat_l (hE : Extensional M) {n} (ρ : Env M n) (B R z F q s t : Term n) :
    Formula.satisfies ρ (aut_eq_m B R z F q s t) ↔
      Aut_eq_d (B.eval ρ) (R.eval ρ) (z.eval ρ) (F.eval ρ) (q.eval ρ) (s.eval ρ) (t.eval ρ) := by
  simp only [aut_eq_m, Aut_eq_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    entry_sat_l M hE, name_sat_l M hE, nmap_sat_l M hE, eq_force_sat_l M hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

variable {B R z F : M.Domain}

theorem aut_eq_push_l (hZF : M.Models ZF) (h : Aut_d M B R z F)
    {x y s t p q} (hx : Name_d M B x) (hy : Name_d M B y)
    (hs : Nmap_d M F x s) (ht : Nmap_d M F y t) (hpq : Entry_d M p q F)
    (he : Eq_force_d M B R z p x y) : Eq_force_d M B R z q s t := by
  let hI : Mem_ind_d M := check_ind_l M hZF
  let hP := KP.exists_pair (ZF.modelsKP hZF)
  have name {a b} (hab : Nmap_d M F a b) : Name_d M B b :=
    nmap_name_l M hZF (fun c d hcd => (h.domain c d hcd).2) hab
  obtain ⟨W, hsW, htW, hW⟩ := name_support_l M hP (KP.exists_union (ZF.modelsKP hZF)) (name hs) (name ht)
  let ρ : Env M 4 := (((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z).push F
  let φ : BinarySchema 5 := {
    body := aut_eq_m (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  obtain ⟨K, hK⟩ := rel_separation_l hZF φ ρ B W
  have hk v a b : Rel_d M K v a b ↔ M.mem v B ∧ M.mem a W ∧ M.mem b W ∧ Aut_eq_d B R z F v a b := by
    simpa only [BinarySchema.denote, φ, aut_eq_sat_l hZF.1] using! hK v a b
  have symm {v a b} (hab : Rel_d M K v a b) : Rel_d M K v b a := by
    obtain ⟨hv, ha, hb, p, x, y, hpv, hx, hy, hxa, hyb, he⟩ := (hk v a b).mp hab
    exact (hk v b a).mpr ⟨hv, hb, ha, p, y, x, hpv, hy, hx, hyb, hxa, eq_force_symm_l hZF hx hy he⟩
  have forth v a b (hab : Rel_d M K v a b) : Match_d M false B R z K v a b := by
    obtain ⟨_, haW, hbW, p, x, y, hpv, hx, hy, hxa, hyb, he⟩ := (hk v a b).mp hab
    intro c d hcd r hr hrd
    obtain ⟨x', d₀, hx'd, hx'c, hd₀d⟩ := (nmap_entry_l M hZF.1 hI hP hxa c d).mp hcd
    obtain ⟨r₀, hr₀r⟩ := h.onto r hr.1
    obtain ⟨r₁, y', e₀, hr₁, hy'e, hr₁e, hx'y'⟩ :=
      ((eq_force_unfold_l M hZF hx hy).mp he).2.1 x' d₀ hx'd r₀
        ((aut_below_l h hpv hr₀r).mpr hr) ((h.order r₀ d₀ r d hr₀r hd₀d).mpr hrd)
    obtain ⟨r₂, hr₁r₂⟩ := h.total r₁ hr₁.1
    obtain ⟨b', hy'b'⟩ := nmap_exists_l M hZF F y'
    obtain ⟨e, he₀e⟩ := h.total e₀ (name_entry_l M hy hy'e).2
    have hb'e := (nmap_entry_l M hZF.1 hI hP hyb b' e).mpr ⟨y', e₀, hy'e, hy'b', he₀e⟩
    exact ⟨r₂, b', e, (aut_below_l h hr₀r hr₁r₂).mp hr₁, hb'e,
      (h.order r₁ e₀ r₂ e hr₁r₂ he₀e).mp hr₁e,
      (hk r₂ c b').mpr ⟨(h.domain r₁ r₂ hr₁r₂).2, (supp_entry_l M hW haW hcd).1,
        (supp_entry_l M hW hbW hb'e).1, r₁, x', y', hr₁r₂,
        (name_entry_l M hx hx'd).1, (name_entry_l M hy hy'e).1, hx'c, hy'b', hx'y'⟩⟩
  refine ⟨(h.domain p q hpq).2, K, ?_, (hk q s t).mpr
    ⟨(h.domain p q hpq).2, hsW, htW, p, x, y, hpq, hx, hy, hs, ht, he⟩⟩
  intro v a b hab
  refine ⟨forth v a b hab, ?_⟩
  intro c d hcd r hr hrd
  obtain ⟨w, e, f, hw, hef, hwf, hce⟩ := forth v b a (symm hab) c d hcd r hr hrd
  exact ⟨w, e, f, hw, hef, hwf, symm hce⟩

theorem aut_eq_force_l (hZF : M.Models ZF) (h : Aut_d M B R z F)
    {x y s t p q} (hx : Name_d M B x) (hy : Name_d M B y)
    (hs : Nmap_d M F x s) (ht : Nmap_d M F y t) (hpq : Entry_d M p q F) :
    Eq_force_d M B R z p x y ↔ Eq_force_d M B R z q s t := by
  refine ⟨aut_eq_push_l hZF h hx hy hs ht hpq, fun he => ?_⟩
  obtain ⟨G, k, hg⟩ := aut_inverse_l hZF h
  exact aut_eq_push_l hZF k (nmap_name_l M hZF (fun a b hab => (h.domain a b hab).2) hs)
    (nmap_name_l M hZF (fun a b hab => (h.domain a b hab).2) ht)
    (aut_nmap_inverse_l hZF h hg hx hs) (aut_nmap_inverse_l hZF h hg hy ht) ((hg q p).mpr hpq) he

theorem aut_mem_push_l (hZF : M.Models ZF) (h : Aut_d M B R z F)
    {x y s t p q} (hx : Name_d M B x) (hy : Name_d M B y)
    (hs : Nmap_d M F x s) (ht : Nmap_d M F y t) (hpq : Entry_d M p q F)
    (hm : Mem_force_d M B R z p x y) : Mem_force_d M B R z q s t := by
  refine ⟨(h.domain p q hpq).2, fun r hr => ?_⟩
  obtain ⟨r₀, hr₀r⟩ := h.onto r hr.1
  obtain ⟨v, a, b, hv, hab, hvb, he⟩ := hm.2 r₀ ((aut_below_l h hpq hr₀r).mpr hr)
  obtain ⟨v', hvv'⟩ := h.total v hv.1
  obtain ⟨a', haa'⟩ := nmap_exists_l M hZF F a
  obtain ⟨b', hbb'⟩ := h.total b (name_entry_l M hy hab).2
  exact ⟨v', a', b', (aut_below_l h hr₀r hvv').mp hv,
    (nmap_entry_l M hZF.1 (check_ind_l M hZF) (KP.exists_pair (ZF.modelsKP hZF)) ht a' b').mpr
      ⟨a, b, hab, haa', hbb'⟩, (h.order v b v' b' hvv' hbb').mp hvb,
    aut_eq_push_l hZF h hx (name_entry_l M hy hab).1 hs haa' hvv' he⟩

theorem aut_mem_force_l (hZF : M.Models ZF) (h : Aut_d M B R z F)
    {x y s t p q} (hx : Name_d M B x) (hy : Name_d M B y)
    (hs : Nmap_d M F x s) (ht : Nmap_d M F y t) (hpq : Entry_d M p q F) :
    Mem_force_d M B R z p x y ↔ Mem_force_d M B R z q s t := by
  refine ⟨aut_mem_push_l hZF h hx hy hs ht hpq, fun he => ?_⟩
  obtain ⟨G, k, hg⟩ := aut_inverse_l hZF h
  exact aut_mem_push_l hZF k (nmap_name_l M hZF (fun a b hab => (h.domain a b hab).2) hs)
    (nmap_name_l M hZF (fun a b hab => (h.domain a b hab).2) ht)
    (aut_nmap_inverse_l hZF h hg hx hs) (aut_nmap_inverse_l hZF h hg hy ht) ((hg q p).mpr hpq) he

end YesMetaZFC.Model.Forcing.Internal
