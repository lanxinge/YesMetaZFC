import YesMetaZFC.Model.Forcing.Internal.Functions.Injection
import YesMetaZFC.Model.Forcing.CCC.Bounds
import YesMetaZFC.Model.Forcing.Internal.Maximum.Basic

/-! # CCC 下可数名称的可能旧成员

单射名称的每个旧目标值只有可数个可能原像，故一个被迫可数的名称只能覆盖
可数多个旧对象。两处泛型论证均经原公式反射消去原模型的外部可数性要求。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain}

theorem inj_name_no_collision_l (O : Cond_order_d M B R z) (hZF : M.Models ZF) {b t w f X Y}
    (hb : M.mem b B) (h : Inj_name_d M B R z b t w f) :
    Neg_d M B R z (Collision_d M B R z b f X Y) b := by
  intro p hp hc
  let ρ : Env M 10 := (((((((((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z).push b).push t).push w).push f).push X).push Y).push p
  let α : Formula 1 10 := .conj (inj_name_m (.bound 9) (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3))
    (.conj (.mem (.bound 6) (.bound 9)) (.conj (below_m (.bound 9) (.bound 8) (.bound 7) (.bound 0) (.bound 6))
      (collision_m (.bound 9) (.bound 8) (.bound 7) (.bound 6) (.bound 3) (.bound 2) (.bound 1) (.bound 0))))
  have spec (N : SetTheory.Structure.{u}) (hE : Extensional N) (η : Env N 10) :
      Formula.satisfies η α ↔ Inj_name_d N (η.bound 9) (η.bound 8) (η.bound 7) (η.bound 6) (η.bound 5) (η.bound 4) (η.bound 3) ∧
        N.mem (η.bound 6) (η.bound 9) ∧ Below_d N (η.bound 9) (η.bound 8) (η.bound 7) (η.bound 0) (η.bound 6) ∧
        Collision_d N (η.bound 9) (η.bound 8) (η.bound 7) (η.bound 6) (η.bound 3) (η.bound 2) (η.bound 1) (η.bound 0) := by
    simp only [α, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, inj_name_sat_l hE, below_sat_l N hE, collision_sat_l N hE]
    rfl
  have bad : Formula.satisfies ρ (.falsum : Formula 1 10) := by
    have hα : α.FreeClosed := by
      simp only [α, Definitional.Formula.FreeClosed]
      exact ⟨inj_name_closed_l _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl, ⟨rfl, rfl⟩,
        below_m_freeClosed _ _ _ _ _ rfl rfl rfl rfl rfl,
        collision_m_freeClosed _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl rfl⟩
    apply source_of_generics_l α .falsum hα (by simp [Definitional.Formula.FreeClosed])
      (.bound 9) (.bound 8) (.bound 7) (.bound 0) rfl rfl rfl rfl
      (fun N hN η L hr U hU hpU => ?_) hZF ρ O hp.1 hp.2.1 ((spec M hZF.1 ρ).mpr ⟨h, hb, hp, hc⟩)
    obtain ⟨hf, hbN, hpb, x, y, v, _, _, _, hyv, hy, hv⟩ := (spec N hN.1 η).mp hr
    have hbU : U (η.bound 6) := hU.upward (η.bound 0) (η.bound 6) hpU hbN hpb.2.2
    obtain ⟨e, he, hm, hi⟩ := check_map_l L hN hU hbU
    obtain ⟨T, ht⟩ := name_value_l (R := η.bound 8) (z := η.bound 7) (U := U) hf.1
    obtain ⟨W, hw⟩ := name_value_l (R := η.bound 8) (z := η.bound 7) (U := U) hf.2.1
    obtain ⟨F, hF⟩ := name_value_l (R := η.bound 8) (z := η.bound 7) (U := U) hf.2.2.1
    have hInj := inj_name_val_l L hN hU hf hbU ht hw hF
    apply (Formula.satisfies_falsum_iff η).mpr
    exact hyv (hi (hInj.2 (e y) (e v) (e x)
      ((value_truth_l L hN hU hbU e hm he hF y x).mp ⟨_, hpU, hy⟩)
      ((value_truth_l L hN hU hbU e hm he hF v x).mp ⟨_, hpU, hv⟩)))
  exact (Formula.satisfies_falsum_iff ρ).mp bad

/-- 被单射名称覆盖的旧对象有一个实际旧目标值及相应原模型条件。 -/
theorem inj_name_value_l (O : Cond_order_d M B R z) (hZF : M.Models ZF) {b t w f X p x s}
    (hb : M.mem b B) (h : Inj_name_d M B R z b t w f) (hX : Check_d M b X w)
    (hp : Below_d M B R z p b) (hx : Check_d M b x s) (hs : Mem_force_d M B R z p s t) :
    ∃ y, M.mem y X ∧ ∃ q, Below_d M B R z q b ∧ Value_d M B R z b f q x y := by
  let ρ : Env M 11 := ((((((((((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z).push b).push t).push w).push f).push X).push p).push x).push s
  let α : Formula 1 11 := .conj (inj_name_m (.bound 10) (.bound 9) (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 4))
    (.conj (.mem (.bound 7) (.bound 10)) (.conj (check_m (.bound 7) (.bound 3) (.bound 5))
      (.conj (below_m (.bound 10) (.bound 9) (.bound 8) (.bound 2) (.bound 7))
        (.conj (check_m (.bound 7) (.bound 1) (.bound 0))
          (mem_force_m (.bound 10) (.bound 9) (.bound 8) (.bound 2) (.bound 0) (.bound 6))))))
  let β : Formula 1 11 := .existsE (.conj (.mem .newest (.bound 4)) (.existsE
    (.conj (below_m (.bound 12) (.bound 11) (.bound 10) .newest (.bound 9))
      (value_m (.bound 12) (.bound 11) (.bound 10) (.bound 9) (.bound 6) .newest (.bound 3) (.bound 1)))))
  have raw (N : SetTheory.Structure.{u}) (hE : Extensional N) (η : Env N 11) :
      Formula.satisfies η α ↔ Inj_name_d N (η.bound 10) (η.bound 9) (η.bound 8) (η.bound 7) (η.bound 6) (η.bound 5) (η.bound 4) ∧
        N.mem (η.bound 7) (η.bound 10) ∧ Check_d N (η.bound 7) (η.bound 3) (η.bound 5) ∧
        Below_d N (η.bound 10) (η.bound 9) (η.bound 8) (η.bound 2) (η.bound 7) ∧
        Check_d N (η.bound 7) (η.bound 1) (η.bound 0) ∧
        Mem_force_d N (η.bound 10) (η.bound 9) (η.bound 8) (η.bound 2) (η.bound 0) (η.bound 6) := by
    simp only [α, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, inj_name_sat_l hE,
      check_sat_l N hE, below_sat_l N hE, mem_force_sat_l N hE]
    rfl
  have out (N : SetTheory.Structure.{u}) (hE : Extensional N) (η : Env N 11) :
      Formula.satisfies η β ↔ ∃ y, N.mem y (η.bound 3) ∧ ∃ q,
        Below_d N (η.bound 10) (η.bound 9) (η.bound 8) q (η.bound 7) ∧
        Value_d N (η.bound 10) (η.bound 9) (η.bound 8) (η.bound 7) (η.bound 4) q (η.bound 1) y := by
    simp only [β, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
      below_sat_l N hE, value_sat_l N hE]
    rfl
  have hα : α.FreeClosed := by
    simp only [α, Definitional.Formula.FreeClosed]
    exact ⟨inj_name_closed_l _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl, ⟨rfl, rfl⟩,
      check_m_freeClosed _ _ _ rfl rfl rfl, below_m_freeClosed _ _ _ _ _ rfl rfl rfl rfl rfl,
      check_m_freeClosed _ _ _ rfl rfl rfl, mem_force_m_freeClosed _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl⟩
  have hβ : β.FreeClosed := by
    simp only [β, Definitional.Formula.FreeClosed]
    exact ⟨⟨rfl, rfl⟩, below_m_freeClosed _ _ _ _ _ rfl rfl rfl rfl rfl,
      value_m_freeClosed _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl rfl⟩
  apply (out M hZF.1 ρ).mp
  apply source_of_generics_l α β hα hβ (.bound 10) (.bound 9) (.bound 8) (.bound 2) rfl rfl rfl rfl
    (fun N hN η L hr U hU hpU => ?_) hZF ρ O hp.1 hp.2.1 ((raw M hZF.1 ρ).mpr ⟨h, hb, hX, hp, hx, hs⟩)
  obtain ⟨hf, hbN, hX, hpb, hx, hs⟩ := (raw N hN.1 η).mp hr
  have hbU := hU.upward (η.bound 2) (η.bound 7) hpU hbN hpb.2.2
  obtain ⟨e, he, hm, _⟩ := check_map_l L hN hU hbU
  obtain ⟨T, ht⟩ := name_value_l (R := η.bound 9) (z := η.bound 8) (U := U) hf.1
  obtain ⟨F, hF⟩ := name_value_l (R := η.bound 9) (z := η.bound 8) (U := U) hf.2.2.1
  have hInj := inj_name_val_l L hN hU hf hbU ht (he _ _ hX) hF
  have hxT := (qval_mem_forcing_l L hN hU (he _ _ hx) ht).mp ⟨_, hpU, hs⟩
  obtain ⟨v, hv, hxv⟩ := hInj.1.2.2 _ hxT
  obtain ⟨y, hy, hye⟩ := (hm _ v).mp hv
  subst v
  obtain ⟨q, hq, hqy⟩ := (value_truth_l L hN hU hbU e hm he hF (η.bound 1) y).mpr hxv
  obtain ⟨r, hr, hrq, hrb⟩ := hU.directed q (η.bound 7) hq hbU
  have hrpos := hU.proper r hr
  exact (out N hN.1 η).mpr ⟨y, hy, r, ⟨hrpos.1, hrpos.2, hrb⟩,
    value_lower_l L _ _ _ _ q r (hU.proper q hq).1 ⟨hrpos.1, hrpos.2, hrq⟩ hqy⟩

/-- CCC 下，能成为同一可数名称成员的全部旧对象构成可数集。 -/
theorem ccc_name_cover_l (O : Cond_order_d M B R z) (hZFC : M.Models ZFC) {ω b t w f Y}
    (hω : M.IsOmega ω) (hb : M.mem b B)
    (hc : Ccc_d M (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) ω B R z)
    (h : Inj_name_d M B R z b t w f) (hw : Check_d M b ω w)
    (hy : ∀ x, M.mem x Y → ∃ p s, Below_d M B R z p b ∧ Check_d M b x s ∧ Mem_force_d M B R z p s t) :
    M.CardinalLessOrEqual (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) Y ω := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  let ρ : Env M 5 := ((((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z).push b).push f
  let φ : BinarySchema 5 := { body := .existsE (.conj (below_m (.bound 7) (.bound 6) (.bound 5) .newest (.bound 4))
    (value_m (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) .newest (.bound 1) (.bound 2))) }
  have hφ n x : φ.denote ρ n x ↔ ∃ q, Below_d M B R z q b ∧ Value_d M B R z b f q x n := by
    simp only [BinarySchema.denote, φ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      below_sat_l M hZF.1, value_sat_l M hZF.1]
    rfl
  obtain ⟨g, hg⟩ := ZF.exists_identityBijection hZF I ω
  apply ZFC.countable_cover_l I hZFC hω φ ρ ⟨g, hg.1⟩
  · intro n hn D hD
    exact ccc_fiber_l O hZFC hc hb hn (inj_name_no_collision_l O hZF hb h)
      (fun x => (hD x).trans (and_congr_right fun _ => hφ n x))
  · intro x hx
    obtain ⟨p, s, hp, hs, ht⟩ := hy x hx
    obtain ⟨n, hn, hv⟩ := inj_name_value_l O hZF hb h hw hp hs ht
    exact ⟨n, hn, (hφ n x).mpr hv⟩

end YesMetaZFC.Model.Forcing.Internal
