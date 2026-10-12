import YesMetaZFC.SetTheory.LargeCardinal.TypeGameAnswer
import YesMetaZFC.SetTheory.Descriptive.FirstViolationRead

/-! # 全部内部有限历史上的逐步检查

三阶段依原时序组合七条规则。空历史通过检查；非空历史只检查最后一步，
此前是否首次违规由独立的有限证据层判断，因而第二方违规后不会重新开局。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Tg_step_d (p : Tg_params_d M.Domain) (i h v : M.Domain) : Prop := ∃ n r,
  M.mem n p.ω ∧ M.IsOrdinalDivision I i p.c n r ∧
    ((r = p.e ∧ Tg_aux_d hZF p n h v) ∨ (r = p.a ∧ Tg_answer_d hZF p n h v) ∨ (r = p.b ∧ M.mem v p.A))

def tg_step_m {d} (p : Tg_params_d (Term d)) (i h v : Term d) : Formula 1 d :=
  .existsE (.existsE (.conj (.mem (.bound 1) p.ω.weaken.weaken) (.conj
    (Formula.isOrdinalDivision kpair_convention_l i.weaken.weaken p.c.weaken.weaken (.bound 1) .newest)
    (.disj (.conj (Formula.extensionalEq .newest p.e.weaken.weaken)
      (tg_aux_m (p.map_l (fun t => t.weaken.weaken)) (.bound 1) h.weaken.weaken v.weaken.weaken))
    (.disj (.conj (Formula.extensionalEq .newest p.a.weaken.weaken)
      (tg_answer_m (p.map_l (fun t => t.weaken.weaken)) (.bound 1) h.weaken.weaken v.weaken.weaken))
      (.conj (Formula.extensionalEq .newest p.b.weaken.weaken) (.mem v.weaken.weaken p.A.weaken.weaken)))))))

@[simp] theorem tg_step_closed_l {d} (p : Tg_params_d (Term d)) (i h v : Term d)
    (hp : p.closed_l) (hi : i.freeSupport = []) (hh : h.freeSupport = []) (hv : v.freeSupport = []) :
    (tg_step_m p i h v).FreeClosed := by
  have hp' : (p.map_l (fun t => t.weaken.weaken)).closed_l := by
    simpa only [Tg_params_d.closed_l, Tg_params_d.map_l, Definitional.Term.freeSupport_weaken] using hp
  rcases hp with ⟨hω, he, ha, hb, hc, _, hA, _⟩
  simp -implicitDefEqProofs [tg_step_m, Definitional.Formula.FreeClosed, hω, he, ha, hb, hc, hA, hi, hh, hv, hp']

theorem tg_step_sat_l {d} (ρ : Env M d) (p : Tg_params_d (Term d)) (i h v : Term d) :
    Formula.satisfies ρ (tg_step_m p i h v) ↔ Tg_step_d hZF (p.map_l (fun t => t.eval ρ)) (i.eval ρ) (h.eval ρ) (v.eval ρ) := by
  simp only [tg_step_m, Tg_step_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_isOrdinalDivision_iff I hZF.1, Formula.satisfies_disj_iff,
    Formula.satisfies_extensionalEq_iff_eq hZF.1, tg_aux_sat_l hZF, tg_answer_sat_l hZF,
    Tg_params_d.map_l, Definitional.Term.eval_weaken]
  rfl

theorem tg_step_read_l {p : Tg_params_d M.Domain} {i n r h v : M.Domain}
    (hi : M.IsOrdinal i) (hc : M.IsOrdinal p.c) (nonzero : ∃ x, M.mem x p.c)
    (hn : M.mem n p.ω) (div : M.IsOrdinalDivision I i p.c n r) :
    Tg_step_d hZF p i h v ↔
      (r = p.e ∧ Tg_aux_d hZF p n h v) ∨ (r = p.a ∧ Tg_answer_d hZF p n h v) ∨ (r = p.b ∧ M.mem v p.A) := by
  obtain ⟨q, s, _, unique⟩ := ZF.ordinalDivision_existsUnique_pair hZF I hi hc nonzero
  obtain ⟨en, er⟩ := unique n r div
  refine ⟨?_, fun h => ⟨n, r, hn, div, h⟩⟩
  rintro ⟨n', r', _, d', rule⟩
  obtain ⟨en', er'⟩ := unique n' r' d'
  exact (en'.trans en.symm) ▸ (er'.trans er.symm) ▸ rule

def Tg_check_d (p : Tg_params_d M.Domain) (X f : M.Domain) : Prop := (∀ v, ¬ M.mem v f) ∨
  ∃ i j h v, M.mem j p.ω ∧ M.SuccessorOf j i ∧ Fn0_d j X f ∧ M.IsRestrictionOf I h f i ∧
    Rd_entry_d i v f ∧ Tg_step_d hZF p i h v

def tg_check_m {d} (p : Tg_params_d (Term d)) (X f : Term d) : Formula 1 d :=
  .disj (Formula.forallMem f .falsum) (.existsE (.existsE (.existsE (.existsE
    (.conj (.mem (.bound 2) p.ω.weaken.weaken.weaken.weaken) (.conj (Formula.isSuccessor (.bound 2) (.bound 3))
      (.conj (fn0_m (.bound 2) X.weaken.weaken.weaken.weaken f.weaken.weaken.weaken.weaken)
        (.conj (Formula.isRestriction kpair_convention_l (.bound 1) f.weaken.weaken.weaken.weaken (.bound 3))
          (.conj (rd_entry0_m (.bound 3) .newest f.weaken.weaken.weaken.weaken)
            (tg_step_m (p.map_l (fun t => t.weaken.weaken.weaken.weaken)) (.bound 3) (.bound 1) .newest))))))))))

@[simp] theorem tg_check_closed_l {d} (p : Tg_params_d (Term d)) (X f : Term d)
    (hp : p.closed_l) (hX : X.freeSupport = []) (hf : f.freeSupport = []) : (tg_check_m p X f).FreeClosed := by
  have hp' : (p.map_l (fun t => t.weaken.weaken.weaken.weaken)).closed_l := by
    simpa only [Tg_params_d.closed_l, Tg_params_d.map_l, Definitional.Term.freeSupport_weaken] using hp
  simp -implicitDefEqProofs [tg_check_m, Definitional.Formula.FreeClosed, hp.1, hX, hf, hp']

theorem tg_check_sat_l {d} (ρ : Env M d) (p : Tg_params_d (Term d)) (X f : Term d) :
    Formula.satisfies ρ (tg_check_m p X f) ↔ Tg_check_d hZF (p.map_l (fun t => t.eval ρ)) (X.eval ρ) (f.eval ρ) := by
  simp only [tg_check_m, Tg_check_d, Formula.satisfies_disj_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_falsum_iff, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_isSuccessor_iff, fn0_sat_l hZF.1,
    Formula.satisfies_isRestriction_iff I, rd_entry0_sat_l hZF.1, tg_step_sat_l hZF,
    Tg_params_d.map_l, Definitional.Term.eval_weaken]
  rfl

/-- 最后一步检查的存在证书由实际追加图唯一确定。 -/
theorem Tg_check_d.end_l {p : Tg_params_d M.Domain} {X i h t a : M.Domain}
    (check : Tg_check_d hZF p X t) (fn : Fn0_d i X h) (endt : Fseq_end_d I p.ω t h a) :
    Tg_step_d hZF p i h a := by
  obtain ⟨m, i', d⟩ := endt
  have eq := d.prefix_sequence.2.2.2.eq hZF.1 (fn0_function_l (ZF.modelsKP hZF) fn).2.1
  subst i'
  rcases check with empty | ⟨k, j, h', a', _, succ, ft, rest, value, step⟩
  · exact (d.last_value.elim fun q hq => empty q hq.2).elim
  · have eq := d.source.2.2.2.eq hZF.1 (fn0_function_l (ZF.modelsKP hZF) ft).2.1
    subst m
    have eq := d.length_successor.predecessor_eq hZF.1 d.prefix_sequence.2.1 succ
    subst k
    have eh := rest.eq hZF.1 d.prefix_restriction
    have ea := d.source.2.2.1.2 i a' a value d.last_value
    exact eh ▸ ea ▸ step

theorem tg_check_end_l {p : Tg_params_d M.Domain} {X i j h t a : M.Domain}
    (hj : M.mem j p.ω) (succ : M.SuccessorOf j i) (fn : Fn0_d j X t)
    (fh : Fn0_d i X h) (endt : Fseq_end_d I p.ω t h a) (step : Tg_step_d hZF p i h a) :
    Tg_check_d hZF p X t := by
  obtain ⟨m, i', d⟩ := endt
  have eq := d.prefix_sequence.2.2.2.eq hZF.1 (fn0_function_l (ZF.modelsKP hZF) fh).2.1
  subst i'
  exact Or.inr ⟨i, j, h, a, hj, succ, fn, d.prefix_restriction, d.last_value, step⟩

def Tg_histories_d (p : Tg_params_d M.Domain) (X F L : M.Domain) : Prop :=
  Fseq_space_d I p.ω X F ∧ ∀ f, M.mem f L ↔ M.mem f F ∧ Tg_check_d hZF p X f

/-- 全体历史与逐步合法集合均存在于原模型中；原公式只使用十二个固定参数。 -/
theorem tg_histories_l (p : Tg_params_d M.Domain) {X : M.Domain} (hω : M.IsOmega p.ω) :
    ∃ F L, Tg_histories_d hZF p X F L := by
  obtain ⟨F, space⟩ := ZF.fseq_space_exists_l I hZF hω X
  let ρ : Env M 13 := ⟨Fin.cases X (Fin.cases p.Q (Fin.cases p.P (Fin.cases p.E (Fin.cases p.ν
    (Fin.cases p.S (Fin.cases p.A (Fin.cases p.δ (Fin.cases p.c (Fin.cases p.b (Fin.cases p.a
      (Fin.cases p.e (fun _ => p.ω)))))))))))), fun _ => p.ω⟩
  let q : Tg_params_d (Term 14) := ⟨.bound 13, .bound 12, .bound 11, .bound 10, .bound 9, .bound 8,
    .bound 7, .bound 6, .bound 5, .bound 4, .bound 3, .bound 2⟩
  let φ : UnarySchema 13 := {
    body := tg_check_m q (.bound 1) .newest
    freeClosed := by
      exact tg_check_closed_l q _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl }
  obtain ⟨L, sep⟩ := ZF.separation_exists_d hZF φ ρ F
  refine ⟨F, L, space, fun f => (sep f).trans (and_congr Iff.rfl ?_)⟩
  exact tg_check_sat_l hZF (ρ.push f) q (.bound 1) .newest

end YesMetaZFC.SetTheory.LargeCardinal
