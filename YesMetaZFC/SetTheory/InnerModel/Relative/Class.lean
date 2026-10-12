import YesMetaZFC.SetTheory.InnerModel.Relative.Hierarchy
import YesMetaZFC.SetTheory.InnerModel.Jensen.Separation

/-! # 相对 J 并类、统一层界与有界分离 -/
namespace YesMetaZFC.SetTheory.InnerModel.Relative
open Definitional.Project
universe u
variable {M : Structure.{u}} (S : M.Domain)

def La_d (x : M.Domain) : Prop := ∃ a Y, Ja_d S a Y ∧ M.mem x Y
def la_m {d} (S x : Term d) : Formula 1 d := .existsE (.existsE
  (.conj (KP.ord0_m (.bound 1)) (.conj (ja_value_m S.weaken.weaken (.bound 1) .newest)
    (.mem x.weaken.weaken .newest))))
derive_free_closed la_m

theorem la_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (S x : Term d) :
    Formula.satisfies ρ (la_m S x) ↔ La_d (S.eval ρ) (x.eval ρ) := by
  simp only [la_m, La_d, Ja_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    KP.ord0_sat_l hKP, ja_value_sat_l, Formula.satisfies_mem_iff, Definitional.Term.eval_weaken]
  exact exists_congr fun _ => exists_congr fun _ => and_assoc.symm

theorem la_transitive_l (hM : M.Models KPi) (hS : M.TransitiveSet S) {x y}
    (hx : La_d S x) (hy : M.mem y x) : La_d S y := by
  obtain ⟨a, Y, ha, hx⟩ := hx
  exact ⟨a, Y, ha, ja_transitive_l S hM hS ha.2 x hx y hy⟩

theorem la_layer_l (hM : M.Models KPi) {a Y} (ha : Ja_d S a Y) : La_d S Y := by
  obtain ⟨s, ho, hs⟩ := KP.ordinal_successor_l (KPi.models_iff_l.mp hM).1 ha.1
  obtain ⟨Z, hz⟩ := ja_value_exists_l S hM s
  exact ⟨s, Z, ⟨ho, hz⟩, ja_mem_l S hM hs.predecessor_mem ha.2 hz⟩

theorem la_seed_l (hM : M.Models KPi) : La_d S S := by
  obtain ⟨e, he⟩ := KP.exists_empty (KPi.models_iff_l.mp hM).1
  obtain ⟨Y, hy⟩ := ja_value_exists_l S hM e
  have h : La_d S Y := la_layer_l S hM (a := e) (Y := Y) ⟨Structure.IsOrdinal.of_no_members he, hy⟩
  have hY : Y = S := ja_zero_l S hM (a := e) (Y := Y) he hy
  exact Eq.mp (congrArg (La_d S) hY) h

def ja_index_s : BinarySchema 1 := {
  body := .conj (KP.ord0_m .newest) (.existsE (.conj (ja_value_m (.bound 3) (.bound 1) .newest)
    (.mem (.bound 2) .newest))) }

theorem ja_index_sat_l (hKP : M.Models KP) (ρ : Env M 1) (x a : M.Domain) :
    ja_index_s.denote ρ x a ↔ ∃ Y, Ja_d (ρ.bound 0) a Y ∧ M.mem x Y := by
  simp only [ja_index_s, BinarySchema.denote, Ja_d, Formula.satisfies_conj_iff,
    Formula.satisfies_exists_iff, KP.ord0_sat_l hKP, ja_value_sat_l, Formula.satisfies_mem_iff]
  exact ⟨fun ⟨ha, Y, hy, hx⟩ => ⟨Y, ⟨ha, hy⟩, hx⟩, fun ⟨Y, ha, hx⟩ => ⟨ha.1, Y, ha.2, hx⟩⟩

def la0_m {d} (S T x : Term d) : Formula 1 d :=
  Formula.existsMem T (Formula.existsMem T.weaken (.conj (KP.ord0_m (.bound 1))
    (.conj (.mem x.weaken.weaken .newest)
      ((rc_value_s ja_op_s).matrix_m (fun _ => S.weaken.weaken) (.bound 1) .newest T.weaken.weaken))))
derive_free_closed la0_m

theorem la0_delta_l {d} (S T x : Term d) : (la0_m S T x).IsDelta0 :=
  .existsMem _ (.existsMem _ (.conj (KP.ord0_delta_l _)
    (.conj (.mem _ _) ((rc_value_s ja_op_s).matrix.delta0.bind_l _))))

def La0_d (T x : M.Domain) : Prop := ∃ a Y, M.mem a T ∧ M.mem Y T ∧ M.IsOrdinal a ∧ M.mem x Y ∧
  ∃ A F, Rc_cert_d ja_op_s (ja_env_l S) A F T ∧ M.mem a A ∧ Rd_entry_d a Y F

theorem la0_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (S T x : Term d) :
    Formula.satisfies ρ (la0_m S T x) ↔ La0_d (S.eval ρ) (T.eval ρ) (x.eval ρ) := by
  have hc (η : Env M 1) a Y W : (rc_value_s ja_op_s).matrix_binary.toBinarySchema.denote
      (η.push a) Y W ↔ ∃ A F, Rc_cert_d ja_op_s (ja_env_l (η.bound 0)) A F W ∧
        M.mem a A ∧ Rd_entry_d a Y F := by
    apply Iff.trans ?_ (rc_matrix_sat_l hKP.1 ja_op_s (ja_env_l (η.bound 0)) a Y W)
    exact Formula.closed_env_l _ (rc_value_s ja_op_s).matrix.freeClosed
      (funext (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))))))
  simp only [la0_m, La0_d, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    KP.ord0_sat_l hKP, Formula.satisfies_mem_iff, S1_binary.matrix_sat_l, hc,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  exact ⟨fun ⟨a, ha, Y, hY, ho, hx, h⟩ => ⟨a, Y, ha, hY, ho, hx, h⟩,
    fun ⟨a, Y, ha, hY, ho, hx, h⟩ => ⟨a, ha, Y, hY, ho, hx, h⟩⟩

def la_s : S1_binary 1 where
  matrix := { body := la0_m (.bound 3) .newest (.bound 2), delta0 := la0_delta_l .. }

theorem la_witness_l (hE : Extensional M) (x : M.Domain) : La_d S x ↔ ∃ T, La0_d S T x := by
  constructor
  · rintro ⟨a, Y, ha, hx⟩
    obtain ⟨T, A, F, hf, hA, hF⟩ := (rc_value_sat_l hE ja_op_s (ja_env_l S) a Y).mp ha.2
    exact ⟨T, a, Y, hf.trans A hf.domain a hA, (hf.function.bound_l hF).2, ha.1, hx, A, F, hf, hA, hF⟩
  · rintro ⟨T, a, Y, _, _, ho, hx, A, F, hf, hA, hF⟩
    exact ⟨a, Y, ⟨ho, (rc_value_sat_l hE ..).mpr ⟨T, A, F, hf, hA, hF⟩⟩, hx⟩

/-- 只收集 Σ₁ 递归证书，再取其中层号的序数界；不使用全收集或选择。 -/
theorem la_bound_l (hM : M.Models KPi) {X} (hx : ∀ x, M.mem x X → La_d S x) :
    ∃ a Y, Ja_d S a Y ∧ M.MemberSubset X Y := by
  let hKP := (KPi.models_iff_l.mp hM).1
  obtain ⟨B, hB⟩ := KP.s1_collection_l hKP la_s (ja_env_l S) X (by
    intro x hxX
    obtain ⟨T, ht⟩ := (la_witness_l S hKP.1 x).mp (hx x hxX)
    exact ⟨x, (S1_binary.sat_l la_s _ x x).mpr ⟨T, (la0_sat_l hKP _ _ _ _).mpr ht⟩⟩)
  obtain ⟨a, ha, hb⟩ := KPi.ordinal_bound_l hM B
  obtain ⟨Y, hy⟩ := ja_value_exists_l S hM a
  refine ⟨a, Y, ⟨ha, hy⟩, fun x hx => ?_⟩
  obtain ⟨_, _, T, hT, ht⟩ := hB x hx
  obtain ⟨b, U, hbT, _, ho, hxU, A, F, hf, hA, hF⟩ := (la0_sat_l hKP _ _ _ _).mp ht
  have hU : Ja_value_d S b U := (rc_value_sat_l hKP.1 ..).mpr ⟨T, A, F, hf, hA, hF⟩
  exact ja_mono_l S hM (ha.transitive b (hb T hT b hbT ho)) hU hy x hxU

theorem la_finite_bound_l (hM : M.Models KPi) {n} (e : Fin n → M.Domain) (he : ∀ i, La_d S (e i)) :
    ∃ a U, Ja_d S a U ∧ ∀ i, M.mem (e i) U := by
  let hKP := (KPi.models_iff_l.mp hM).1
  induction n with
  | zero =>
    obtain ⟨a, ha⟩ := KP.exists_empty hKP
    obtain ⟨U, hu⟩ := ja_value_exists_l S hM a
    exact ⟨a, U, ⟨Structure.IsOrdinal.of_no_members ha, hu⟩, fun i => Fin.elim0 i⟩
  | succ n ih =>
    obtain ⟨a, U, ha, hU⟩ := ih (fun i => e i.succ) (fun i => he i.succ)
    obtain ⟨T, ht⟩ := KP.exists_insert hKP U (e 0)
    obtain ⟨b, V, hb, hv⟩ := la_bound_l S hM (X := T) (fun x hx => ((ht x).mp hx).elim
      (fun hx => ⟨a, U, ha, hx⟩) (fun hx => hx.symm ▸ he 0))
    exact ⟨b, V, hb, Fin.cases (hv _ ((ht _).mpr (Or.inr rfl)))
      (fun i => hv _ ((ht _).mpr (Or.inl (hU i))))⟩

theorem la_separation_l (hM : M.Models KPi) (hS : M.TransitiveSet S) {n} (φ : Delta0UnarySchema n)
    (ρ : Env M n) (hρ : ∀ i, La_d S (ρ.bound i)) {X} (hX : La_d S X) :
    ∃ Y, La_d S Y ∧ ∀ x, M.mem x Y ↔ M.mem x X ∧ φ.toUnarySchema.denote ρ x := by
  obtain ⟨a, U, ha, hU⟩ := la_finite_bound_l S hM (ρ.push X).bound (Fin.cases hX hρ)
  obtain ⟨s, ho, hs⟩ := KP.ordinal_successor_l ((KPi.models_iff_l.mp hM).1) ha.1
  obtain ⟨C, hc⟩ := ja_value_exists_l S hM s
  have hstep := jh_step_spec_l hM (ja_successor_l S hM ha.1 hs ha.2 hc)
  obtain ⟨Y, hy, hY⟩ := rd_separation_l ((KPi.models_iff_l.mp hM).1) hstep.1 (ja_transitive_l S hM hS hc)
    hstep.2.2 (ja_transitive_l S hM hS ha.2) φ ρ (fun i => hU i.succ) (hU 0)
  exact ⟨Y, ⟨s, C, ⟨ho, hc⟩, hy⟩, hY⟩

theorem la_ordinal_l (hM : M.Models KPi) (hS : M.TransitiveSet S) {a} (ha : M.IsOrdinal a) : La_d S a := by
  let hKP := (KPi.models_iff_l.mp hM).1
  let φ : UnarySchema 1 := { body := .imp (KP.ord0_m .newest) (la_m (.bound 1) .newest) }
  have hφ b : φ.denote (ja_env_l S) b ↔ (M.IsOrdinal b → La_d S b) := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_imp_iff, KP.ord0_sat_l hKP, la_sat_l hKP]; rfl
  apply (hφ a).mp ((KPi.models_iff_l.mp hM).2 φ (ja_env_l S) ?_ a) ha
  intro b ih
  apply (hφ b).mpr
  intro hb
  obtain ⟨c, U, hc, hU⟩ := la_bound_l S hM (fun x hx => (hφ x).mp (ih x hx) (hb.mem hx))
  let ψ : Delta0UnarySchema 0 := { body := KP.ord0_m .newest, delta0 := KP.ord0_delta_l _ }
  obtain ⟨D, hd, hD'⟩ := la_separation_l S hM hS ψ (jh_env_l a) (fun i => Fin.elim0 i) (la_layer_l S hM hc)
  have hD x : M.mem x D ↔ M.mem x U ∧ M.IsOrdinal x :=
    (hD' x).trans (and_congr_right fun _ => KP.ord0_sat_l hKP _ _)
  have ht : M.TransitiveSet D := fun x hx y hy => (hD y).mpr
    ⟨ja_transitive_l S hM hS hc.2 x ((hD x).mp hx).1 y hy, ((hD x).mp hx).2.mem hy⟩
  have ho := KP.ordinal_of_transitive_l hKP ht (fun x hx => ((hD x).mp hx).2)
  have hsub : M.MemberSubset b D := fun x hx => (hD x).mpr ⟨hU x hx, hb.mem hx⟩
  rcases Structure.IsOrdinal.trichotomy hKP.1 hb ho (KP.difference_exists_d hKP)
      (KP.intersection_exists_d hKP b D) with he | he | he
  · exact (hKP.1.eq_of_same_members b D he).symm ▸ hd
  · exact la_transitive_l S hM hS hd he
  · exact (KP.mem_irrefl_d hKP D (hsub D he)).elim

end YesMetaZFC.SetTheory.InnerModel.Relative
