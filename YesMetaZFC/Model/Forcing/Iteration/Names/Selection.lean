import YesMetaZFC.Model.Forcing.Iteration.Names.Quotient
import YesMetaZFC.Model.Forcing.Internal.Maximum.Pool

/-! # 随前缀泛型变化的后继坐标

商条件名称在稠密处决定一个旧条件。不同决定分支相交时，规范名称忠实性
迫使两个旧条件相同；故其后继坐标可在原名称库中混合，无须加强给定前缀。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}}

def Row_pick_d (α B R b t D N τ s p : M.Domain) : Prop :=
  ∃ r a v, M.mem r D ∧ M.mem r N ∧ M.mem a B ∧ Row_append_d M α t a s r ∧
    Check_d M b r v ∧ Below_d M B R B p a ∧ Eq_force_d M B R B p τ v

def row_pick_m {n} (α B R b t D N τ s p : Term n) : Formula 1 n :=
  .existsE (.existsE (.existsE
    (.conj (.mem (.bound 2) D.weaken.weaken.weaken)
      (.conj (.mem (.bound 2) N.weaken.weaken.weaken)
        (.conj (.mem (.bound 1) B.weaken.weaken.weaken)
          (.conj (row_append_m α.weaken.weaken.weaken t.weaken.weaken.weaken
            (.bound 1) s.weaken.weaken.weaken (.bound 2))
            (.conj (check_m b.weaken.weaken.weaken (.bound 2) .newest)
              (.conj (below_m B.weaken.weaken.weaken R.weaken.weaken.weaken B.weaken.weaken.weaken
                p.weaken.weaken.weaken (.bound 1))
                (eq_force_m B.weaken.weaken.weaken R.weaken.weaken.weaken B.weaken.weaken.weaken
                  p.weaken.weaken.weaken τ.weaken.weaken.weaken .newest)))))))))
derive_free_closed row_pick_m

theorem row_pick_sat_l (hE : Extensional M) {n} (ρ : Env M n) (α B R b t D N τ s p : Term n) :
    Formula.satisfies ρ (row_pick_m α B R b t D N τ s p) ↔
      Row_pick_d (M := M) (α.eval ρ) (B.eval ρ) (R.eval ρ) (b.eval ρ) (t.eval ρ)
        (D.eval ρ) (N.eval ρ) (τ.eval ρ) (s.eval ρ) (p.eval ρ) := by
  simp only [row_pick_m, Row_pick_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, row_append_sat_l M hE, check_sat_l M hE,
    below_sat_l M hE, eq_force_sat_l M hE, Definitional.Term.eval_weaken]
  rfl

/-- 商成员力迫直接给出稠密的旧条件决定分支。 -/
theorem row_pick_dense_l (hZF : M.Models ZF) {α B R b A T t W C S D V N K τ p}
    (h : Row_stage_d M α B R b) (hStep : Two_step_d M B R B b A T W C S)
    (k : Row_repr_d M α t C S D V)
    (hK : Row_quot_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) α B b D N K)
    (hτ : Mem_force_d M B R B p τ K) :
    Dense_d M B R B (fun a => ∃ s, Row_pick_d (M := M) α B R b t D N τ s a) p := by
  intro q hq
  obtain ⟨a, haq, r, c, v, hr, hrN, hc, hcr, hrv, hac, he⟩ := row_quot_decide_l hK hτ q hq
  obtain ⟨x, hx, c', s, hxc, hcsr⟩ := (k.conditions r).mp hr
  have hc' := ((two_step_mem_l hStep hxc).mp hx).2.1.1
  have hec := hcr.eq hZF.1 ⟨(h.rows c' hc').graph,
    row_append_prefix_l (KP.mem_irrefl_d (ZF.modelsKP hZF) α) (h.rows c' hc') hcsr⟩
  subst c'
  exact ⟨a, haq, s, r, c, v, hr, hrN, hc, hcsr, hrv, hac, he⟩

/-- 后继坐标的混合保持在已经装配的名称库内，并在每个决定分支上取正确值。 -/
theorem row_select_l (hZF : M.Models ZF) {α B R b A T t W C S D V N K τ p}
    (h : Row_stage_d M α B R b) (hStep : Two_step_d M B R B b A T W C S)
    (hPool : Name_pool_d M B A t W) (k : Row_repr_d M α t C S D V)
    (hK : Row_quot_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) α B b D N K)
    (hτ : Name_d M B τ)
    (hm : Mem_force_d M B R B p τ K) : ∃ u,
    M.mem u W ∧ Mem_force_d M B R B p u A ∧
    ∀ s a, Row_pick_d (M := M) α B R b t D N τ s a → Eq_force_d M B R B a u s := by
  let ρ₀ : Env M 4 := (((⟨fun _ => α, fun _ => α⟩ : Env M 1).push B).push R).push b
  let ρ : Env M 8 := (((ρ₀.push t).push D).push N).push τ
  let φ : BinarySchema 8 := {
    body := row_pick_m (.bound 9) (.bound 8) (.bound 7) (.bound 6) (.bound 5)
      (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have hφ s a : φ.denote ρ s a ↔ Row_pick_d (M := M) α B R b t D N τ s a :=
    row_pick_sat_l hZF.1 _ _ _ _ _ _ _ _ _ _ _
  have hn s (hs : M.mem s W) : Name_d M B s := ⟨W, hs, hStep.closed⟩
  obtain ⟨u, hu, hmix⟩ := name_pool_mix_l h.order hZF hPool φ ρ (by
    intro a c s s' d ha hc hs hs' hp hp' hda hdc
    obtain ⟨r, a', v, _, _, ha', har, hv, _, he⟩ := (hφ s a).mp hp
    obtain ⟨r', c', v', _, _, hc', hcr, hv', _, he'⟩ := (hφ s' c).mp hp'
    have hvn := check_name_l M (check_range_l M hZF) h.base hv
    have hvn' := check_name_l M (check_range_l M hZF) h.base hv'
    have hvv := eq_force_trans_l h.order hZF hvn hτ hvn'
      (eq_force_symm_l hZF hτ hvn (eq_force_lower_l h.order hZF hτ hvn a d ha hda he))
      (eq_force_lower_l h.order hZF hτ hvn' c d hc hdc he')
    have hrr := check_force_reflect_l h.order hZF h.base hv hv'
      ⟨hda.1, hda.2.1, h.top d hda.1⟩ hvv
    subst r'
    have heq := (row_append_injective_l hZF.1 (KP.mem_irrefl_d (ZF.modelsKP hZF) α)
      (h.rows a' ha') (h.rows c' hc') har hcr).2
    exact heq ▸ eq_force_refl_l h.order hZF hda.1 (hn s hs))
  have sel s a (ha : Row_pick_d (M := M) α B R b t D N τ s a) : Eq_force_d M B R B a u s := by
    obtain ⟨r, c, v, hr, hrN, hc, hcr, hv, hac, he⟩ := ha
    have hs := (row_repr_decode_l hZF h hStep k hr hc hcr).1
    exact hmix a s hac.1 hs ((hφ s a).mpr ⟨r, c, v, hr, hrN, hc, hcr, hv, hac, he⟩)
  refine ⟨u, hu, mem_force_dense_l h.order hm.1 (fun q hq => ?_), sel⟩
  obtain ⟨a, haq, s, hs⟩ := row_pick_dense_l hZF h hStep k hK hm q hq
  have hes := sel s a hs
  obtain ⟨r, c, v, hr, _, hc, hcr, _, hac, _⟩ := hs
  obtain ⟨hsW, hsA, _⟩ := row_repr_decode_l hZF h hStep k hr hc hcr
  exact ⟨a, haq, mem_force_left_l h.order hZF (hn s hsW) (hn u hu) (hn A hStep.root)
    (eq_force_symm_l hZF (hn u hu) (hn s hsW) hes)
      ((regular_mem_l h.order s A).1 c a hc hac hsA)⟩

/-- 选出的名称解释为被商条件名称选中的旧条件的后继坐标。 -/
theorem row_select_value_l (hZF : M.Models ZF) {α B R b A T t W C S D V N K τ p u}
    (h : Row_stage_d M α B R b) (hStep : Two_step_d M B R B b A T W C S)
    (k : Row_repr_d M α t C S D V)
    (hK : Row_quot_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) α B b D N K)
    (hτ : Name_d M B τ) (hm : Mem_force_d M B R B p τ K)
    (hs : ∀ s a, Row_pick_d (M := M) α B R b t D N τ s a → Eq_force_d M B R B a u s)
    {U} (hU : Generic_d M B R B U) (hp : U p)
    {x y : (extension_l M hZF B R B U).Domain}
    (hτx : Qval_d M B R B U τ x) (huy : Qval_d M B R B U u y)
    (e : M.Domain → (extension_l M hZF B R B U).Domain)
    (he : ∀ r v, Check_d M b r v → Qval_d M B R B U v (e r)) :
    ∃ r a s, M.mem r D ∧ M.mem r N ∧ Row_append_d M α t a s r ∧ U a ∧
      e r = x ∧ Qval_d M B R B U s y := by
  obtain ⟨Y, hY⟩ := name_value_l (R := R) (z := B) (U := U) hK.1
  have hxY := (qval_mem_forcing_l h.order hZF hU hτx hY).mp ⟨p, hp, hm⟩
  obtain ⟨r, a, hr, hrN, har', ha, hrx⟩ := (row_quot_value_l hZF h.order hU hK hY e he x).mp hxY
  obtain ⟨w, hw, a', s, hwa, har⟩ := (k.conditions r).mp hr
  have ha' := ((two_step_mem_l hStep hwa).mp hw).2.1.1
  have heq := har'.eq hZF.1 ⟨(h.rows a' ha').graph,
    row_append_prefix_l (KP.mem_irrefl_d (ZF.modelsKP hZF) α) (h.rows a' ha') har⟩
  subst a'
  obtain ⟨v, hv, hvN, _⟩ := zf_check_l M hZF h.base r
  have hvx : Qval_d M B R B U v x := hrx ▸ he r v hv
  obtain ⟨c, hc, heq⟩ := (qval_eq_l h.order hZF hU hτx hvx).mpr rfl
  obtain ⟨d, hd, hdc, hda⟩ := hU.directed c a hc ha
  have hd' := hU.proper d hd
  have ha' := hU.proper a ha
  have hdu := hs s d ⟨r, a, v, hr, hrN, ha'.1, har, hv, ⟨hd'.1, hd'.2, hda⟩,
    eq_force_lower_l h.order hZF hτ hvN c d (hU.proper c hc).1 ⟨hd'.1, hd'.2, hdc⟩ heq⟩
  have hsN : Name_d M B s := ⟨W, (row_repr_decode_l hZF h hStep k hr ha'.1 har).1, hStep.closed⟩
  obtain ⟨y', hy'⟩ := name_value_l (R := R) (z := B) (U := U) hsN
  have hyy := (qval_eq_l h.order hZF hU huy hy').mp ⟨d, hd, hdu⟩
  exact ⟨r, a, s, hr, hrN, har, ha, hrx, hyy.symm ▸ hy'⟩

end YesMetaZFC.Model.Forcing.Internal
