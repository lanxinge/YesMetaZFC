import YesMetaZFC.SetTheory.InnerModel.Relative.Hierarchy
import YesMetaZFC.SetTheory.InnerModel.Jensen.Separation
import YesMetaZFC.Model.SetTheory.ProjectBounded
import YesMetaZFC.Model.SetTheory.LevyReflection.Relativization
import YesMetaZFC.Model.SetTheory.LevyReflection.Closure
import YesMetaZFC.SetTheory.InnerModel.Jensen.ZF.Separation
import YesMetaZFC.SetTheory.Descriptive.Topology.Space
import YesMetaZFC.SetTheory.TransitiveClosure
import YesMetaZFC.Model.SetTheory.Internal.RealTrace
import YesMetaZFC.Model.SetTheory.Truth.SetTruthReals

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

/-! ## 相对 J 并类的实际结构与基础封闭性 -/
namespace YesMetaZFC.SetTheory.InnerModel.Relative
open Definitional.Project
universe u
variable {M : Structure.{u}} (S : M.Domain)

def la_model_l (hM : M.Models KPi) : Structure.{u} where
  Domain := {x : M.Domain // La_d S x}
  nonempty := ⟨⟨S, la_seed_l S hM⟩⟩
  mem x y := M.mem x.val y.val

theorem la_model_ext_l (hM : M.Models KPi) (hS : M.TransitiveSet S) : Extensional (la_model_l S hM) := by
  refine ⟨fun a b h => Subtype.ext ((KPi.models_iff_l.mp hM).1.1.eq_of_same_members a.val b.val (fun x => ?_))⟩
  exact ⟨fun hx => (h ⟨x, la_transitive_l S hM hS a.property hx⟩).mp hx,
    fun hx => (h ⟨x, la_transitive_l S hM hS b.property hx⟩).mpr hx⟩

theorem la_model_delta_l (hM : M.Models KPi) (hS : M.TransitiveSet S) {n} {φ : Formula 1 n} (hφ : φ.IsDelta0)
    (ρ : Env (la_model_l S hM) n) :
    Formula.satisfies ρ φ ↔ Formula.satisfies (image_env_l (M := la_model_l S hM) (N := M) Subtype.val ρ) φ :=
  delta0_image_l (M := la_model_l S hM) (N := M) Subtype.val (fun _ _ h => Subtype.ext h)
    (fun a y => ⟨fun h => ⟨⟨y, la_transitive_l S hM hS a.property h⟩, h, rfl⟩,
      fun ⟨_, hx, he⟩ => he ▸ hx⟩) hφ ρ

theorem la_closed_l (hM : M.Models KPi) (k : Rd_sym) {a b c t}
    (ha : La_d S a) (hb : La_d S b) (hc : La_d S c) (ht : Rd_fun_d k a b c t) : La_d S t := by
  let e : Fin 3 → M.Domain := Fin.cases a (Fin.cases b (Fin.cases c Fin.elim0))
  obtain ⟨i, U, hi, hU⟩ := la_finite_bound_l S hM e
    (Fin.cases ha (Fin.cases hb (Fin.cases hc (fun i => Fin.elim0 i))))
  obtain ⟨s, ho, hs⟩ := KP.ordinal_successor_l ((KPi.models_iff_l.mp hM).1) hi.1
  obtain ⟨V, hv⟩ := ja_value_exists_l S hM s
  have h := jh_step_spec_l hM (ja_successor_l S hM hi.1 hs hi.2 hv)
  exact ⟨s, V, ⟨ho, hv⟩, h.1 k a b c (h.2.1 a (hU 0)) (h.2.1 b (hU 1)) (h.2.1 c (hU 2)) t ht⟩

theorem la_model_separation_l (hM : M.Models KPi) (hS : M.TransitiveSet S) {n} (φ : Delta0UnarySchema n)
    (ρ : Env (la_model_l S hM) n) (X : (la_model_l S hM).Domain) :
    ∃ Y : (la_model_l S hM).Domain, ∀ x,
      M.mem x.val Y.val ↔ M.mem x.val X.val ∧ φ.toUnarySchema.denote ρ x := by
  obtain ⟨Y, hy, hY⟩ := la_separation_l S hM hS φ (image_env_l (M := la_model_l S hM) (N := M) Subtype.val ρ)
    (fun i => by exact (ρ.bound i).property) X.property
  refine ⟨⟨Y, hy⟩, fun x => (hY x.val).trans (and_congr_right fun _ => ?_)⟩
  have h := la_model_delta_l S hM hS φ.delta0 (ρ.push x)
  rw [image_env_push_l (M := la_model_l S hM) (N := M) Subtype.val ρ x] at h
  exact h.symm

end YesMetaZFC.SetTheory.InnerModel.Relative

/-! ## 原公式在相对 J 并类中的统一相对化 -/
namespace YesMetaZFC.SetTheory.InnerModel.Relative
open Definitional.Project
universe u
variable {M : Structure.{u}}

def la_rel_m : {n d : Nat} → Formula 1 n → Term d → (Fin n → Term d) → Formula 1 d
  | _, _, .falsum, _, _ => .falsum
  | _, _, .truth, _, _ => .truth
  | _, _, .mem s t, _, e => .mem (s.bind e) (t.bind e)
  | _, _, .atom r hr ts, _, e => .atom r hr (ts.bind e)
  | _, _, .neg φ, A, e => .neg (la_rel_m φ A e)
  | _, _, .conj φ ψ, A, e => .conj (la_rel_m φ A e) (la_rel_m ψ A e)
  | _, _, .disj φ ψ, A, e => .disj (la_rel_m φ A e) (la_rel_m ψ A e)
  | _, _, .imp φ ψ, A, e => .imp (la_rel_m φ A e) (la_rel_m ψ A e)
  | _, _, .iff φ ψ, A, e => .iff (la_rel_m φ A e) (la_rel_m ψ A e)
  | _, _, .existsE φ, A, e => .existsE (.conj (la_m A.weaken .newest)
      (la_rel_m φ A.weaken (Fin.cases .newest (fun i => (e i).weaken))))
  | _, _, .forallE φ, A, e => .forallE (.imp (la_m A.weaken .newest)
      (la_rel_m φ A.weaken (Fin.cases .newest (fun i => (e i).weaken))))

@[simp] theorem la_rel_closed_l {n d} (φ : Formula 1 n) (hφ : φ.FreeClosed)
    (A : Term d) (e : Fin n → Term d) (hA : A.freeSupport = []) (he : ∀ i, (e i).freeSupport = []) :
    (la_rel_m φ A e).FreeClosed := by
  induction φ generalizing d <;> simp only [Definitional.Formula.FreeClosed] at hφ
  case falsum | truth => simp only [la_rel_m, Definitional.Formula.FreeClosed]
  case mem s t =>
    simp only [la_rel_m, Definitional.Formula.FreeClosed]
    exact ⟨(Definitional.Term.freeSupport_bind_of_closed e he s).trans hφ.1,
      (Definitional.Term.freeSupport_bind_of_closed e he t).trans hφ.2⟩
  case atom _ _ ts =>
    simp only [la_rel_m, Definitional.Formula.FreeClosed]
    exact (Definitional.TermVector.freeClosed_bind_iff_of_closed e he ts).mpr hφ
  case neg φ ih =>
    simp only [la_rel_m, Definitional.Formula.FreeClosed]
    exact ih hφ A e hA he
  case conj φ ψ ih jh | disj φ ψ ih jh | imp φ ψ ih jh | iff φ ψ ih jh =>
    simp only [la_rel_m, Definitional.Formula.FreeClosed]
    exact ⟨ih hφ.1 A e hA he, jh hφ.2 A e hA he⟩
  case existsE φ ih | forallE φ ih =>
    simp only [la_rel_m, Definitional.Formula.FreeClosed]
    exact ⟨la_m_freeClosed A.weaken .newest (by simpa using hA) rfl,
      ih hφ A.weaken _ (by simpa using hA) (Fin.cases rfl (fun i => by simpa using he i))⟩

private theorem la_bind_sat_l (hM : M.Models KPi) (A : M.Domain) (hA : M.TransitiveSet A) {n d}
    (φ : Formula 1 n) (hφ : φ.FreeClosed) (hδ : φ.IsDelta0) (η : Env (la_model_l A hM) n)
    (ρ : Env M d) (e : Fin n → Term d) (he : ∀ i, (e i).eval ρ = (η.bound i).val) :
    Formula.satisfies ρ (φ.bind e) ↔ Formula.satisfies η φ := by
  rw [Formula.satisfies_bind]
  exact (lr_env_congr_l φ hφ _ (image_env_l Subtype.val η) he).trans (la_model_delta_l A hM hA hδ η).symm

theorem la_rel_sat_l (hM : M.Models KPi) (A : M.Domain) (hA : M.TransitiveSet A) {n d}
    (φ : Formula 1 n) (hφ : φ.FreeClosed) (η : Env (la_model_l A hM) n)
    (ρ : Env M d) (T : Term d) (e : Fin n → Term d) (hT : T.eval ρ = A)
    (he : ∀ i, (e i).eval ρ = (η.bound i).val) :
    Formula.satisfies ρ (la_rel_m φ T e) ↔ Formula.satisfies η φ := by
  induction φ generalizing d <;> simp only [Definitional.Formula.FreeClosed] at hφ
  case falsum | truth => simp only [la_rel_m, Formula.satisfies_falsum_iff, Formula.satisfies_truth_iff]
  case mem s t =>
    exact la_bind_sat_l hM A hA (.mem s t)
      (by simpa only [Definitional.Formula.FreeClosed] using hφ) (.mem _ _) η ρ e he
  case atom r hr ts =>
    exact la_bind_sat_l hM A hA (.atom r hr ts)
      (by simpa only [Definitional.Formula.FreeClosed] using hφ) (.atom _ _ _) η ρ e he
  case neg φ ih => simpa only [la_rel_m, Formula.satisfies_neg_iff] using not_congr (ih hφ η ρ T e hT he)
  case conj φ ψ ih jh | disj φ ψ ih jh | imp φ ψ ih jh | iff φ ψ ih jh =>
    simp only [la_rel_m, Formula.satisfies_conj_iff, Formula.satisfies_disj_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_iff_iff, ih hφ.1 η ρ T e hT he, jh hφ.2 η ρ T e hT he]
  case existsE φ ih | forallE φ ih =>
    have tr (x : (la_model_l A hM).Domain) := ih hφ (η.push x) (ρ.push x.val) T.weaken
      (Fin.cases .newest (fun i => (e i).weaken)) (by simpa using hT)
      (Fin.cases rfl (fun i => (Definitional.Term.eval_weaken ρ x.val (e i)).trans (he i)))
    first
    | simp only [la_rel_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, la_sat_l (KPi.models_iff_l.mp hM).1,
        Definitional.Term.eval_weaken, Definitional.Term.eval_newest, hT]
      exact ⟨fun ⟨x, hx, h⟩ => ⟨⟨x, hx⟩, (tr ⟨x, hx⟩).mp h⟩,
        fun ⟨x, h⟩ => ⟨x.val, x.property, (tr x).mpr h⟩⟩
    | simp only [la_rel_m, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, la_sat_l (KPi.models_iff_l.mp hM).1,
        Definitional.Term.eval_weaken, Definitional.Term.eval_newest, hT]
      exact ⟨fun h x => (tr x).mp (h x.val x.property), fun h x hx => (tr ⟨x, hx⟩).mpr (h ⟨x, hx⟩)⟩

end YesMetaZFC.SetTheory.InnerModel.Relative

/-! ## 相对 J 层上的有限公式反射

背景反射同时封闭后继、带基集的层值和成员的层号见证。反射域的相对 J 部分
由同一递归唯一性识别为实际极限层；基集始终作为内部参数保留。
-/
namespace YesMetaZFC.SetTheory.InnerModel.Relative
open Definitional.Project
universe u
variable {M : Structure.{u}} (S : M.Domain)

def ja_succ_s : UnarySchema 1 := { body := KP.succ0_m .newest (.bound 1) }
def ja_stage_s : UnarySchema 2 := { body := ja_value_m (.bound 2) (.bound 1) .newest }
def ja_index_query_s : UnarySchema 2 := { body := ja_index_s.body, freeClosed := ja_index_s.freeClosed }
def ja_cut_queries_l : Lr_family := [⟨1, ja_succ_s⟩, ⟨2, ja_stage_s⟩, ⟨2, ja_index_query_s⟩]

theorem ja_cut_l (hM : M.Models KPi) {V} (ht : M.TransitiveSet V) (hSV : M.mem S V)
    (he : ∃ e, (∀ x, ¬ M.mem x e) ∧ M.mem e V) (hc : Lr_step_d ja_cut_queries_l V V) :
    ∃ a U, Ja_d S a U ∧ ∀ x, M.mem x U ↔ M.mem x V ∧ La_d S x := by
  let hKP := (KPi.models_iff_l.mp hM).1
  let φ : Delta0UnarySchema 0 := { body := KP.ord0_m .newest, delta0 := KP.ord0_delta_l _ }
  obtain ⟨a, ha'⟩ := KP.separation_exists_d hKP φ (jh_env_l V) V
  have ha b : M.mem b a ↔ M.mem b V ∧ M.IsOrdinal b :=
    (ha' b).trans (and_congr_right fun _ => KP.ord0_sat_l hKP _ _)
  have hta : M.TransitiveSet a := fun b hb c hcb =>
    (ha c).mpr ⟨ht b ((ha b).mp hb).1 c hcb, ((ha b).mp hb).2.mem hcb⟩
  have hoa := KP.ordinal_of_transitive_l hKP hta (fun b hb => ((ha b).mp hb).2)
  have hs b (hb : M.mem b a) : ∃ s, M.mem s a ∧ M.mem b s := by
    obtain ⟨s, ho, hs⟩ := KP.ordinal_successor_l hKP ((ha b).mp hb).2
    let ρ := rd_seed_env_l b
    obtain ⟨t, htV, hp⟩ := hc ⟨1, ja_succ_s⟩ (by simp [ja_cut_queries_l]) ρ
      (fun _ => ((ha b).mp hb).1) ⟨s, (KP.succ0_sat_l hKP.1 (ρ.push s) .newest (.bound 1)).mpr hs⟩
    have hts := (KP.succ0_sat_l hKP.1 (ρ.push t) .newest (.bound 1)).mp hp
    change M.SuccessorOf t b at hts
    have eq := Structure.SuccessorOf.eq hKP.1 hts hs
    exact ⟨t, (ha t).mpr ⟨htV, eq.symm ▸ ho⟩, hts.predecessor_mem⟩
  obtain ⟨e, hem, heV⟩ := he
  have hl : M.IsLimitOrdinal a := ⟨hoa, ⟨e, (ha e).mpr ⟨heV, Structure.IsOrdinal.of_no_members hem⟩⟩, hs⟩
  have stage b (hb : M.mem b V) : ∃ Y, M.mem Y V ∧ Ja_value_d S b Y := by
    obtain ⟨Y, hy⟩ := ja_value_exists_l S hM b
    let ρ := (ja_env_l S).push b
    obtain ⟨Z, hz, hp⟩ := hc ⟨2, ja_stage_s⟩ (by simp [ja_cut_queries_l]) ρ
      (Fin.cases hb (fun _ => hSV)) ⟨Y, (ja_value_sat_l (ρ.push Y) (.bound 2) (.bound 1) .newest).mpr hy⟩
    exact ⟨Z, hz, (ja_value_sat_l (ρ.push Z) (.bound 2) (.bound 1) .newest).mp hp⟩
  obtain ⟨U, hu⟩ := ja_value_exists_l S hM a
  refine ⟨a, U, ⟨hoa, hu⟩, fun x => ?_⟩
  constructor
  · intro hx
    obtain ⟨b, hb, Y, hy, hx⟩ := (ja_limit_l S hM hl hu x).mp hx
    obtain ⟨Z, hz, hp⟩ := stage b ((ha b).mp hb).1
    have hyV : M.mem Y V := (ja_value_unique_l S hM hy hp).symm ▸ hz
    exact ⟨ht Y hyV x hx, b, Y, ⟨((ha b).mp hb).2, hy⟩, hx⟩
  · rintro ⟨hxV, b, Y, hb, hxY⟩
    let ρ := (ja_env_l S).push x
    obtain ⟨c, hcV, hp⟩ := hc ⟨2, ja_index_query_s⟩ (by simp [ja_cut_queries_l]) ρ
      (Fin.cases hxV (fun _ => hSV)) ⟨b, (ja_index_sat_l hKP (ja_env_l S) x b).mpr ⟨Y, hb, hxY⟩⟩
    obtain ⟨Z, hz, hx⟩ := (ja_index_sat_l hKP (ja_env_l S) x c).mp hp
    exact (ja_limit_l S hM hl hu x).mpr ⟨c, (ha c).mpr ⟨hcV, hz.1⟩, Z, hz.2, hx⟩

def ja_query_s {n} (φ : UnarySchema n) : UnarySchema (n+1) := {
  body := .conj (la_m (.bound 1) .newest)
    (la_rel_m φ.body (.bound 1) (Fin.cases .newest (fun i => .bound ⟨i.val+2, by omega⟩)))
  freeClosed := by
    simp only [Definitional.Formula.FreeClosed]
    exact ⟨la_m_freeClosed _ _ rfl rfl,
      la_rel_closed_l _ φ.freeClosed _ _ rfl (Fin.cases rfl (fun _ => rfl))⟩ }
def ja_queries_l (Φ : Lr_family) : Lr_family := Φ.map (fun q => ⟨q.1+1, ja_query_s q.2⟩)

theorem ja_query_sat_l (hM : M.Models KPi) (hS : M.TransitiveSet S) {n} (φ : UnarySchema n)
    (ρ : Env (la_model_l S hM) n) (x : (la_model_l S hM).Domain) :
    (ja_query_s φ).denote ((image_env_l (N := M) Subtype.val ρ).push S) x.val ↔ φ.denote ρ x := by
  let η := (image_env_l (N := M) Subtype.val ρ).push S
  let e : Fin (n+1) → Term (n+2) := Fin.cases .newest (fun i => .bound ⟨i.val+2, by omega⟩)
  have tr := la_rel_sat_l hM S hS φ.body φ.freeClosed (ρ.push x) (η.push x.val) (.bound 1) e
    rfl (Fin.cases rfl (fun _ => rfl))
  rw [ja_query_s, UnarySchema.denote, Formula.satisfies_conj_iff, la_sat_l (KPi.models_iff_l.mp hM).1]
  exact (and_iff_right x.property).trans tr

theorem ja_closed_layer_l (hZF : M.Models ZF) (hS : M.TransitiveSet S) (Φ : Lr_family)
    (A : (la_model_l S (ZF.models_kpi_l hZF)).Domain) :
    ∃ a, ∃ U : (la_model_l S (ZF.models_kpi_l hZF)).Domain, Ja_d S a U.val ∧
      M.mem A.val U.val ∧ Lr_step_d Φ U U := by
  let hM := ZF.models_kpi_l hZF
  let hKP := ZF.modelsKP hZF
  let N := la_model_l S hM
  obtain ⟨ω, hω⟩ := ZF.exists_omega hZF
  obtain ⟨e, he⟩ := KP.exists_empty hKP
  obtain ⟨P, hp⟩ := kp_finite_cover_l hKP [A.val, S, e]
  obtain ⟨_, V, hv, _, hpV, hc⟩ := ZF.lr_closed_layer_l (kp_pair_l hKP) hZF hω
    (ja_cut_queries_l ++ ja_queries_l Φ) P
  have ht := v_transitive_l (kp_pair_l hKP) hv
  have hSV := ht P hpV S (hp S (by simp)).2
  obtain ⟨a, U, ha, hcut⟩ := ja_cut_l S hM ht hSV
    ⟨e, he, ht P hpV e (hp e (by simp)).2⟩ (fun q hq => hc q (List.mem_append_left _ hq))
  let W : N.Domain := ⟨U, la_layer_l S hM ha⟩
  refine ⟨a, W, ha, (hcut A.val).mpr ⟨ht P hpV A.val (hp A.val (by simp)).2, A.property⟩, ?_⟩
  intro q hq ρ hρ hx
  let η := (image_env_l (M := N) (N := M) Subtype.val ρ).push S
  obtain ⟨x, hx⟩ := hx
  obtain ⟨y, hyV, hy⟩ := hc ⟨q.1+1, ja_query_s q.2⟩
    (List.mem_append_right _ (List.mem_map.mpr ⟨q, hq, rfl⟩)) η
    (Fin.cases hSV (fun i => ((hcut _).mp (hρ i)).1))
    ⟨x.val, (ja_query_sat_l S hM hS q.2 ρ x).mpr hx⟩
  have hyL : La_d S y := by
    have h := (Formula.satisfies_conj_iff _ _ _).mp hy
    exact (la_sat_l hKP (η.push y) (.bound 1) .newest).mp h.1
  exact ⟨⟨y, hyL⟩, (hcut y).mpr ⟨hyV, hyL⟩, (ja_query_sat_l S hM hS q.2 ρ ⟨y, hyL⟩).mp hy⟩

end YesMetaZFC.SetTheory.InnerModel.Relative

/-! ## 相对 J 并类的全分离、全收集和内部幂集 -/
namespace YesMetaZFC.SetTheory.InnerModel.Relative
open Definitional.Project
universe u
variable {M : Structure.{u}} (S : M.Domain) (hZF : M.Models ZF) (hS : M.TransitiveSet S)
local notation "Nₛ" => la_model_l S (ZF.models_kpi_l hZF)
include hZF hS

theorem la_full_separation_l {n} (φ : UnarySchema n) (ρ : Env Nₛ n) (X : (Nₛ).Domain) :
    ∃ Y : (Nₛ).Domain, ∀ x, (Nₛ).mem x Y ↔ (Nₛ).mem x X ∧ φ.denote ρ x := by
  -- 有限反射把全公式化为真实层上的有界公式，再调用 rud 闭包中的分离。
  let hM := ZF.models_kpi_l hZF
  obtain ⟨b, T, hb, hT⟩ := la_finite_bound_l S (ZF.models_kpi_l hZF) (fun i => ((ρ.push X).bound i).val)
    (fun i => ((ρ.push X).bound i).property)
  let A : (Nₛ).Domain := ⟨T, la_layer_l S hM hb⟩
  obtain ⟨a, U, ha, hAU, hc⟩ := ja_closed_layer_l S hZF hS (lr_queries_l φ.body φ.freeClosed) A
  have ht : (Nₛ).TransitiveSet U := fun x hx y hy => ja_transitive_l S hM hS ha.2 x.val hx y.val hy
  have hX : (Nₛ).mem X U := ja_transitive_l S hM hS ha.2 T hAU X.val (hT 0)
  have hρ i : (Nₛ).mem (ρ.bound i) U := ja_transitive_l S hM hS ha.2 T hAU _ (hT i.succ)
  let e : Fin (n+1) → Term (n+2) := Fin.cases .newest (fun i => .bound ⟨i.val+2, by omega⟩)
  let ψ : Delta0UnarySchema (n+1) := {
    body := lr_rel_m φ.body (.bound 1) e
    freeClosed := lr_rel_closed_l _ φ.freeClosed _ _ rfl (Fin.cases rfl (fun _ => rfl))
    delta0 := lr_rel_delta_l .. }
  have tr x (hx : (Nₛ).mem x X) : φ.denote ρ x ↔ ψ.toUnarySchema.denote (ρ.push U) x :=
    lr_reflect_core_l φ.body φ.freeClosed hc (ρ.push x) ((ρ.push U).push x) (.bound 1) e
      rfl (Fin.cases rfl (fun _ => rfl)) (Fin.cases (ht X hX x hx) hρ)
  obtain ⟨Y, hy⟩ := la_model_separation_l S (ZF.models_kpi_l hZF) hS ψ (ρ.push U) X
  exact ⟨Y, fun x => (hy x).trans (and_congr_right fun hx => (tr x hx).symm)⟩

omit hS in
theorem la_trace_l (B : M.Domain) : ∃ D, ∀ x, M.mem x D ↔ M.mem x B ∧ La_d S x := by
  let φ : UnarySchema 1 := { body := la_m (.bound 1) .newest }
  obtain ⟨D, hd⟩ := ZF.separation_exists_d hZF φ (ja_env_l S) B
  exact ⟨D, fun x => (hd x).trans (and_congr_right fun _ => la_sat_l (ZF.modelsKP hZF) _ _ _)⟩

theorem la_full_collection_l {n} (φ : BinarySchema n) (ρ : Env Nₛ n) (X : (Nₛ).Domain)
    (ht : ∀ x, (Nₛ).mem x X → ∃ y, φ.denote ρ x y) :
    ∃ Y : (Nₛ).Domain, ∀ x, (Nₛ).mem x X → ∃ y, (Nₛ).mem y Y ∧ φ.denote ρ x y := by
  -- 背景收集只产生一个见证池；取并类迹及统一层界，才得到内模型自己的收集集。
  let η := (image_env_l (M := Nₛ) (N := M) Subtype.val ρ).push S
  let e : Fin (n+2) → Term (n+3) := Fin.cases .newest (Fin.cases (.bound 1) (fun i => .bound ⟨i.val+3, by omega⟩))
  let ψ : BinarySchema (n+1) := {
    body := .conj (la_m (.bound 2) .newest) (la_rel_m φ.body (.bound 2) e)
    freeClosed := by
      simp only [Definitional.Formula.FreeClosed]
      exact ⟨la_m_freeClosed _ _ rfl rfl,
        la_rel_closed_l _ φ.freeClosed _ _ rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))⟩ }
  have sat x y : ψ.denote η x y ↔ La_d S y ∧
      Formula.satisfies ((η.push x).push y) (la_rel_m φ.body (.bound 2) e) := by
    simp only [BinarySchema.denote, ψ, Formula.satisfies_conj_iff, la_sat_l (ZF.modelsKP hZF)]; rfl
  have tr (x y : (Nₛ).Domain) : Formula.satisfies ((η.push x.val).push y.val)
      (la_rel_m φ.body (.bound 2) e) ↔ φ.denote ρ x y :=
    la_rel_sat_l (ZF.models_kpi_l hZF) S hS φ.body φ.freeClosed ((ρ.push x).push y) ((η.push x.val).push y.val)
      (.bound 2) e rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))
  obtain ⟨B, hB⟩ := ZF.collection_exists_d hZF ψ η X.val (fun x hx => by
    let z : (Nₛ).Domain := ⟨x, la_transitive_l S (ZF.models_kpi_l hZF) hS X.property hx⟩
    obtain ⟨y, hy⟩ := ht z hx
    exact ⟨y.val, (sat x y.val).mpr ⟨y.property, (tr z y).mpr hy⟩⟩)
  obtain ⟨D, hd⟩ := la_trace_l S hZF B
  obtain ⟨a, Y, ha, hy⟩ := la_bound_l S (ZF.models_kpi_l hZF) (fun x hx => ((hd x).mp hx).2)
  refine ⟨⟨Y, la_layer_l S (ZF.models_kpi_l hZF) ha⟩, fun x hx => ?_⟩
  obtain ⟨y, hyB, hp⟩ := hB x.val hx
  obtain ⟨hyL, hyφ⟩ := (sat x.val y).mp hp
  exact ⟨⟨y, hyL⟩, hy y ((hd y).mpr ⟨hyB, hyL⟩), (tr x ⟨y, hyL⟩).mp hyφ⟩

theorem la_model_power_l (X : (Nₛ).Domain) : ∃ P : (Nₛ).Domain, (Nₛ).IsPowerSetOf P X := by
  -- 仅将属于并类的旧幂集成员纳入层界，不假定内模型拥有背景的全部子集。
  have sub (x : (Nₛ).Domain) : (Nₛ).MemberSubset x X ↔ M.MemberSubset x.val X.val :=
    ⟨fun h y hy => h ⟨y, la_transitive_l S (ZF.models_kpi_l hZF) hS x.property hy⟩ hy,
      fun h y hy => h y.val hy⟩
  obtain ⟨P, hp⟩ := ZF.exists_powerSet hZF X.val
  obtain ⟨D, hd⟩ := la_trace_l S hZF P
  obtain ⟨a, U, ha, hu⟩ := la_bound_l S (ZF.models_kpi_l hZF) (fun x hx => ((hd x).mp hx).2)
  let W : (Nₛ).Domain := ⟨U, la_layer_l S (ZF.models_kpi_l hZF) ha⟩
  let φ : Delta0UnarySchema 1 := { body := Formula.subset .newest (.bound 1), delta0 := .atom _ _ _ }
  obtain ⟨Q, hq⟩ := la_model_separation_l S (ZF.models_kpi_l hZF) hS φ (rd_seed_env_l (M := Nₛ) X) W
  have hq' (x : (Nₛ).Domain) : (Nₛ).mem x Q ↔ (Nₛ).mem x W ∧ (Nₛ).MemberSubset x X :=
    (hq x).trans (and_congr_right fun _ => Formula.satisfies_subset_iff _ _ _)
  exact ⟨Q, fun x => (hq' x).trans ⟨And.right,
    fun hx => ⟨hu x.val ((hd x.val).mpr ⟨(hp x.val).mpr ((sub x).mp hx), x.property⟩), hx⟩⟩⟩

end YesMetaZFC.SetTheory.InnerModel.Relative

/-! ## 任意传递基集上的 Jensen 并类满足原 ZF -/
namespace YesMetaZFC.SetTheory.InnerModel.Relative
open Definitional.Project
universe u
variable {M : Structure.{u}} (S : M.Domain) (hZF : M.Models ZF) (hS : M.TransitiveSet S)

include hS

theorem la_model_zf_l : (la_model_l S (ZF.models_kpi_l hZF)).Models ZF := by
  let hM := ZF.models_kpi_l hZF
  let N := la_model_l S hM
  have hE := la_model_ext_l S (ZF.models_kpi_l hZF) hS
  have same (x y : N.Domain) : N.SameMembers x y ↔ x.val = y.val :=
    ⟨fun h => congrArg Subtype.val (hE.eq_of_same_members x y h),
      fun h => (show x = y from Subtype.ext h) ▸ (fun _ => Iff.rfl)⟩
  refine ⟨hE, fun s hs => ?_⟩
  rw [Structure.satisfiesSentence_iff]
  intro f
  cases hs with
  | extensionality =>
    simp only [Axioms.extensionality, Sentence.ofFormula, Formula.satisfies_forall_iff,
      Formula.satisfies_imp_iff, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff,
      Formula.satisfies_extensionalEq_iff_eq hE]
    exact hE.eq_of_same_members
  | emptySet =>
    obtain ⟨e, he⟩ := KP.exists_empty (ZF.modelsKP hZF)
    exact (Axioms.satisfies_emptySet_iff f).mpr
      ⟨⟨e, la_ordinal_l S (ZF.models_kpi_l hZF) hS (Structure.IsOrdinal.of_no_members he)⟩, fun z => he z.val⟩
  | pairing =>
    apply (Axioms.satisfies_pairing_iff f).mpr
    intro x y
    obtain ⟨p, hp⟩ := KP.exists_pair (ZF.modelsKP hZF) x.val y.val
    exact ⟨⟨p, la_closed_l S (ZF.models_kpi_l hZF) .pair x.property y.property y.property hp⟩,
      fun z => (hp z.val).trans (or_congr (same z x).symm (same z y).symm)⟩
  | union =>
    apply (Axioms.satisfies_union_iff f).mpr
    intro x
    obtain ⟨y, hy⟩ := KP.exists_union (ZF.modelsKP hZF) x.val
    refine ⟨⟨y, la_closed_l S (ZF.models_kpi_l hZF) .union x.property x.property x.property hy⟩, fun z => (hy z.val).trans ?_⟩
    exact ⟨fun ⟨a, ha, hz⟩ => ⟨⟨a, la_transitive_l S hM hS x.property ha⟩, ha, hz⟩,
      fun ⟨a, ha, hz⟩ => ⟨a.val, ha, hz⟩⟩
  | powerSet => exact (Axioms.satisfies_powerSet_iff f).mpr (la_model_power_l S hZF hS)
  | infinity =>
    apply (Axioms.satisfies_infinity_iff f).mpr
    obtain ⟨ω, hω⟩ := ZF.exists_omega hZF
    have hL := la_ordinal_l S (ZF.models_kpi_l hZF) hS (hω.isOrdinal (ZF.modelsKP hZF))
    refine ⟨⟨ω, hL⟩, ?_, fun x hx => ?_⟩
    · obtain ⟨e, he, heω⟩ := hω.1.1
      exact ⟨⟨e, la_transitive_l S hM hS hL heω⟩, fun z => he z.val, heω⟩
    · obtain ⟨s, hs, hsω⟩ := hω.1.2 x.val hx
      refine ⟨⟨s, la_transitive_l S hM hS hL hsω⟩, fun z => (hs z.val).trans (or_congr_right ?_), hsω⟩
      exact ⟨fun h v => h v.val, fun h => (same z x).mp h ▸ (fun _ => Iff.rfl)⟩
  | foundation =>
    apply (Axioms.foundation_sat_iff_d f).mpr
    intro x hx
    obtain ⟨z, hz⟩ := hx
    obtain ⟨a, ha, hm⟩ := KP.mem_minimal_exists_d (ZF.modelsKP hZF) ⟨z.val, hz⟩
    exact ⟨⟨a, la_transitive_l S hM hS x.property ha⟩, ha, fun z hz => hm z.val hz⟩
  | separation φ =>
    apply (Formula.satisfies_forallClosure_iff f (Axioms.Schema.separationCore φ)).mpr
    intro b
    exact (Axioms.Schema.separation_sat_iff_d ⟨b, f⟩ φ).mpr (la_full_separation_l S hZF hS φ ⟨b, f⟩)
  | collection φ =>
    apply (Formula.satisfies_forallClosure_iff f (Axioms.Schema.collectionCore φ)).mpr
    intro b
    exact (Axioms.Schema.collection_sat_iff_d ⟨b, f⟩ φ).mpr (la_full_collection_l S hZF hS φ ⟨b, f⟩)

end YesMetaZFC.SetTheory.InnerModel.Relative

/-! ## L(ℝ) 的实际构造与实数保持

实数固定为 Kuratowski 编码的内部 ω→ω 函数。起层为 TC({ℝ})，
继承相对 Jensen 递归；全部序数和原实数都属于并类。背景仅需 ZF。
-/
namespace YesMetaZFC.SetTheory.InnerModel.Relative
open Definitional.Project Descriptive
universe u
variable {M : Structure.{u}} (S : M.Domain) (hZF : M.Models ZF) (hS : M.TransitiveSet S)

local notation "Nₛ" => la_model_l S (ZF.models_kpi_l hZF)

/-- 函数图的绝对性通过已有的 Δ₀ 有界图公式取得。 -/
theorem la_function_l (A B F : (Nₛ).Domain) :
    (Nₛ).IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP (la_model_zf_l S hZF hS))) F A B ↔
      M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) F.val A.val B.val := by
  let ρ : Env Nₛ 3 := ⟨Fin.cases F (Fin.cases B (fun _ => A)), fun _ => A⟩
  have h := la_model_delta_l S (ZF.models_kpi_l hZF) hS (fn0_delta_l (.bound 2) (.bound 1) (.bound 0)) ρ
  rw [fn0_sat_l (la_model_ext_l S (ZF.models_kpi_l hZF) hS), fn0_sat_l hZF.1] at h
  exact ⟨fun hf => fn0_function_l (ZF.modelsKP hZF)
    (h.mp (fn0_of_function_l (ZF.modelsKP (la_model_zf_l S hZF hS)) hf)),
    fun hf => fn0_function_l (ZF.modelsKP (la_model_zf_l S hZF hS))
      (h.mpr (fn0_of_function_l (ZF.modelsKP hZF) hf))⟩

/-- 最小归纳集在相对内模型与背景中相同，包括非标准自然数。 -/
theorem la_omega_l {ω : M.Domain} (hω : M.IsOmega ω) :
    (Nₛ).IsOmega ⟨ω, la_ordinal_l S (ZF.models_kpi_l hZF) hS (hω.isOrdinal (ZF.modelsKP hZF))⟩ := by
  let hM := ZF.models_kpi_l hZF
  have same (a b : (Nₛ).Domain) : (Nₛ).SameMembers a b ↔ a.val = b.val :=
    ⟨fun h => congrArg Subtype.val ((la_model_ext_l S (ZF.models_kpi_l hZF) hS).eq_of_same_members a b h),
      fun h => (show a = b from Subtype.ext h) ▸ (fun _ => Iff.rfl)⟩
  have hL := la_ordinal_l S (ZF.models_kpi_l hZF) hS (hω.isOrdinal (ZF.modelsKP hZF))
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · obtain ⟨e, he, heω⟩ := hω.1.1
    exact ⟨⟨e, la_transitive_l S hM hS hL heω⟩, fun z => he z.val, heω⟩
  · intro x hx
    obtain ⟨s, hs, hsω⟩ := hω.1.2 x.val hx
    exact ⟨⟨s, la_transitive_l S hM hS hL hsω⟩,
      fun z => (hs z.val).trans (or_congr_right
        ⟨fun h v => h v.val, fun h => (same z x).mp h ▸ (fun _ => Iff.rfl)⟩), hsω⟩
  · intro T hT x hx
    apply hω.2 T.val (show M.IsInductive T.val from ?_) x.val hx
    refine ⟨?_, fun a ha => ?_⟩
    · obtain ⟨e, he, heT⟩ := hT.1
      exact ⟨e.val, fun z hz => he ⟨z, la_transitive_l S hM hS e.property hz⟩ hz, heT⟩
    · let a' : (Nₛ).Domain := ⟨a, la_transitive_l S hM hS T.property ha⟩
      obtain ⟨s, hs, hsT⟩ := hT.2 a' ha
      refine ⟨s.val, fun z => ⟨fun hz => ?_, fun hz => ?_⟩, hsT⟩
      · let z' : (Nₛ).Domain := ⟨z, la_transitive_l S hM hS s.property hz⟩
        exact ((hs z').mp hz).imp_right (fun h => by
          have he : z = a := (same z' a').mp h
          subst z
          exact fun _ => Iff.rfl)
      · rcases hz with hz | hz
        · exact (hs ⟨z, la_transitive_l S hM hS a'.property hz⟩).mpr (Or.inl hz)
        · have he := hZF.1.eq_of_same_members z a hz
          exact he.symm ▸ hs.predecessor_mem

omit S hS in
def Lr_seed_d (ω B T : M.Domain) : Prop :=
  Baire_d (kp_pair_l (ZF.modelsKP hZF)) ω B ∧ Tc_d B T

omit S hS in
theorem lr_seed_exists_l : ∃ ω B T, Lr_seed_d hZF ω B T := by
  obtain ⟨ω, hω⟩ := ZF.exists_omega hZF
  obtain ⟨B, hB⟩ := baire_exists_l (kp_pair_l (ZF.modelsKP hZF)) hZF hω
  obtain ⟨T, hT⟩ := ZF.tc_exists_l (kp_pair_l (ZF.modelsKP hZF)) hZF B
  exact ⟨ω, B, T, hB, hT⟩

omit hS in
/-- 无新实数等价只需在实际并类上成立，即可识别其中的完整 Baire 空间。 -/
theorem la_reals_l {ω B : M.Domain} (hw : M.IsOmega ω) (tc : Tc_d B S)
    (reals : ∀ x, La_d S x → (Fn0_d ω ω x ↔ M.mem x B)) :
    ∃ w r : (Nₛ).Domain, w.val = ω ∧ r.val = B ∧
      Baire_d (kp_pair_l (ZF.modelsKP (la_model_zf_l S hZF tc.1))) w r := by
  let w : (Nₛ).Domain := ⟨ω,la_ordinal_l S (ZF.models_kpi_l hZF) tc.1 (hw.isOrdinal (ZF.modelsKP hZF))⟩
  let r : (Nₛ).Domain := ⟨B,la_transitive_l S (ZF.models_kpi_l hZF) tc.1
    (la_seed_l S (ZF.models_kpi_l hZF)) tc.2.1⟩
  exact ⟨w,r,rfl,rfl,la_omega_l S hZF tc.1 hw,fun f => (reals f.val f.property).symm.trans
    ((Iff.intro (fn0_function_l (ZF.modelsKP hZF)) (fn0_of_function_l (ZF.modelsKP hZF))).trans
      (la_function_l S hZF tc.1 w w f).symm)⟩

end YesMetaZFC.SetTheory.InnerModel.Relative

/-! ## 无选择的规范 L(ℝ) 模型

以唯一实数基集的存在量词定义成员类，再直接取子类型隶属结构。
不通过 Classical.choose 选择 ω、实数空间、传递闭包或模型。
-/
namespace YesMetaZFC.SetTheory.InnerModel.Relative
open Definitional.Project Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)

theorem lr_seed_unique_l {ω B S v C T : M.Domain} (h : Lr_seed_d hZF ω B S) (k : Lr_seed_d hZF v C T) :
    ω = v ∧ B = C ∧ S = T := by
  have ev : ω = v := hZF.1.eq_of_same_members ω v (fun n =>
    ⟨h.1.1.2 v k.1.1.1 n, k.1.1.2 ω h.1.1.1 n⟩)
  subst v
  have eB := baire_unique_l (kp_pair_l (ZF.modelsKP hZF)) hZF.1 h.1 k.1
  subst C
  exact ⟨rfl, rfl, tc_unique_l hZF.1 h.2 k.2⟩

def Lr_d (x : M.Domain) : Prop := ∃ ω B S, Lr_seed_d hZF ω B S ∧ La_d S x

theorem lr_iff_l {ω B S : M.Domain} (h : Lr_seed_d hZF ω B S) (x : M.Domain) :
    Lr_d hZF x ↔ La_d S x := by
  refine ⟨?_, fun hx => ⟨ω, B, S, h, hx⟩⟩
  rintro ⟨v, C, T, k, hx⟩
  exact (lr_seed_unique_l hZF k h).2.2 ▸ hx

/-! 固定一个 `Lr` 种子后，任意 `Lr` 对象都能在同一个 `L[A]` 载体中读取。
这为后续把 `L(ℝ)` 内的收益集合送入单个相对模型的决定性证明提供统一入口。 -/
theorem lr_object_in_seed_l {ω B S x : M.Domain}
    (h : Lr_seed_d hZF ω B S) (hx : Lr_d hZF x) :
    La_d S x :=
  (lr_iff_l hZF h x).mp hx

theorem lr_reals_in_seed_l {ω B S : M.Domain}
    (h : Lr_seed_d hZF ω B S) : La_d S B := by
  exact la_transitive_l S (ZF.models_kpi_l hZF) h.2.1
    (la_seed_l S (ZF.models_kpi_l hZF)) h.2.2.1

theorem lr_subset_in_seed_l {ω B S A D : M.Domain}
    (seed : Lr_seed_d hZF ω B S) (hA : Lr_d hZF A) (hD : Lr_d hZF D)
    (sub : M.MemberSubset A D) :
    (la_model_l S (ZF.models_kpi_l hZF)).MemberSubset
      ⟨A, lr_object_in_seed_l hZF seed hA⟩ ⟨D, lr_object_in_seed_l hZF seed hD⟩ := by
  intro x hx
  exact sub x.val hx

def lr_m {d} (x : Term d) : Formula 1 d := .existsE (.existsE (.existsE
  (.conj (baire_m (𝒞 := kpair_convention_l) (.bound 2) (.bound 1))
    (.conj (tc_m (.bound 1) .newest) (la_m .newest x.weaken.weaken.weaken)))))
derive_free_closed lr_m

theorem lr_sat_l {d} (ρ : Env M d) (x : Term d) :
    Formula.satisfies ρ (lr_m x) ↔ Lr_d hZF (x.eval ρ) := by
  simp only [lr_m, Lr_d, Lr_seed_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    baire_sat_l (kp_pair_l (ZF.modelsKP hZF)) hZF.1, tc_sat_l, la_sat_l (ZF.modelsKP hZF),
    Definitional.Term.eval_weaken]
  exact exists_congr fun ω => exists_congr fun B => exists_congr fun S => and_assoc.symm

def lr_model_l : Structure.{u} where
  Domain := {x : M.Domain // Lr_d hZF x}
  nonempty := (lr_seed_exists_l hZF).elim fun ω h => h.elim fun B h => h.elim fun S h =>
    ⟨⟨S, ω, B, S, h, la_seed_l S (ZF.models_kpi_l hZF)⟩⟩
  mem x y := M.mem x.val y.val

/-- 唯一起层识别两种构造；等式只使用谓词外延性，不选择任何集合。 -/
theorem lr_model_eq_l {ω B S : M.Domain} (h : Lr_seed_d hZF ω B S) :
    lr_model_l hZF = la_model_l S (ZF.models_kpi_l hZF) := by
  have he : Lr_d hZF = La_d S := funext (fun x => propext (lr_iff_l hZF h x))
  have lift (P Q : M.Domain → Prop) (hp : Nonempty {x // P x}) (hq : Nonempty {x // Q x}) (e : P = Q) :
      ({ Domain := {x // P x}, nonempty := hp, mem := fun x y => M.mem x.val y.val } : Structure) =
      { Domain := {x // Q x}, nonempty := hq, mem := fun x y => M.mem x.val y.val } := by cases e; rfl
  exact lift _ _ _ _ he

theorem lr_model_zf_l : (lr_model_l hZF).Models ZF := by
  obtain ⟨ω, B, S, h⟩ := lr_seed_exists_l hZF
  rw [lr_model_eq_l hZF h]
  exact la_model_zf_l S hZF h.2.1

theorem lr_transitive_l {x y : M.Domain} (hx : Lr_d hZF x) (hy : M.mem y x) : Lr_d hZF y := by
  obtain ⟨ω, B, S, h, hx⟩ := hx
  exact ⟨ω, B, S, h, la_transitive_l S (ZF.models_kpi_l hZF) h.2.1 hx hy⟩

theorem lr_ordinal_l {a : M.Domain} (ha : M.IsOrdinal a) : Lr_d hZF a := by
  obtain ⟨ω, B, S, h⟩ := lr_seed_exists_l hZF
  exact ⟨ω, B, S, h, la_ordinal_l S (ZF.models_kpi_l hZF) h.2.1 ha⟩

/-- 模型的包含映射保持全部原实数，不仅保持已选的外部标准序列。 -/
theorem lr_real_l {ω B x : M.Domain} (hB : Baire_d (kp_pair_l (ZF.modelsKP hZF)) ω B)
    (hx : M.mem x B) : Lr_d hZF x := by
  obtain ⟨S, hS⟩ := ZF.tc_exists_l (kp_pair_l (ZF.modelsKP hZF)) hZF B
  have hM := ZF.models_kpi_l hZF
  exact ⟨ω, B, S, ⟨hB, hS⟩, la_transitive_l S hM hS.1
    (la_transitive_l S hM hS.1 (la_seed_l S hM) hS.2.1) hx⟩

end YesMetaZFC.SetTheory.InnerModel.Relative

/-! ## 同基集相对 Jensen 层的绝对性及存在见证上传

相对递归的实际 Σ₁ 证书沿成员满嵌入向外保持，唯一性识别同一层。
层中见证属于原 L(ℝ)，故其 Δ₀ 矩阵可直接反射；结论使用原对象语言满足关系。
-/
namespace YesMetaZFC.SetTheory.InnerModel.Relative
open Definitional.Project Internal
universe u v
variable {M : Structure.{u}} {N : Structure.{v}}

private theorem s1_image_l (e : M.Domain → N.Domain) (inj : Function.Injective e)
    (full : ∀ a y, N.mem y (e a) ↔ ∃ b, M.mem b a ∧ e b = y)
    {n} (φ : S1_binary n) (ρ : Env M n) {α Y : M.Domain} (h : φ.schema.denote ρ α Y) :
    φ.schema.denote (image_env_l e ρ) (e α) (e Y) := by
  obtain ⟨W,hw⟩ := (φ.sat_l ρ α Y).mp h
  apply (φ.sat_l (image_env_l e ρ) (e α) (e Y)).mpr
  refine ⟨e W,?_⟩
  have transferred := (delta0_image_l e inj full φ.matrix.delta0 (((ρ.push α).push Y).push W)).mp hw
  have env : image_env_l e (((ρ.push α).push Y).push W) =
      (((image_env_l e ρ).push (e α)).push (e Y)).push (e W) := by
    rw [image_env_push_l,image_env_push_l,image_env_push_l]
  exact env ▸ transferred

theorem ja_value_image_l (e : M.Domain → N.Domain) (inj : Function.Injective e)
    (full : ∀ a y, N.mem y (e a) ↔ ∃ b, M.mem b a ∧ e b = y)
    {S α Y : M.Domain} (h : Ja_value_d S α Y) : Ja_value_d (e S) (e α) (e Y) :=
  s1_image_l e inj full (rc_value_s ja_op_s) (ja_env_l S) h

/-- 两个模型在共同背景中识别种子及序数后，其实际递归层也识别。 -/
theorem ja_common_layer_l {D : Structure} (hM : M.Models KPi) (hN : N.Models KPi) (hD : D.Models KPi)
    (e : M.Domain → D.Domain) (ei : Function.Injective e)
    (ef : ∀ a y, D.mem y (e a) ↔ ∃ b, M.mem b a ∧ e b = y)
    (f : N.Domain → D.Domain) (fi : Function.Injective f)
    (ff : ∀ a y, D.mem y (f a) ↔ ∃ b, N.mem b a ∧ f b = y)
    {S α : M.Domain} {T β : N.Domain} (seed : e S = f T) (index : e α = f β)
    (oa : M.IsOrdinal α) (ob : N.IsOrdinal β) :
    ∃ U V, Ja_d S α U ∧ Ja_d T β V ∧ e U = f V := by
  obtain ⟨U,hu⟩ := ja_value_exists_l S hM α
  obtain ⟨V,hv⟩ := ja_value_exists_l T hN β
  have image := ja_value_image_l e ei ef hu
  rw [seed,index] at image
  exact ⟨U,V,⟨oa,hu⟩,⟨ob,hv⟩,ja_value_unique_l (f T) hD image (ja_value_image_l f fi ff hv)⟩

variable (hM : M.Models ZF) {c P R : M.Domain}
  (model : Smem_d (kp_pair_l (ZF.modelsKP hM)) c P R) (trans : M.TransitiveSet P)
  (native : (smdl_structure_l (kp_pair_l (ZF.modelsKP hM)) (R := R) model.1.2.1).Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hM)
include trans native

theorem lr_layer_upload_l {ω B S α : (smdl_structure_l I (R := R) model.1.2.1).Domain}
    (seed : Lr_seed_d native ω B S)
    (ordinal : (smdl_structure_l I (R := R) model.1.2.1).IsOrdinal α) :
    ∃ Z : (smdl_structure_l I (R := R) model.1.2.1).Domain, Ja_d S α Z ∧
      (∀ Y, Ja_value_d S.val α.val Y ↔ Y = Z.val) ∧
      ∀ {n} (φ : Delta0UnarySchema n) (ρ : Env (lr_model_l native) n),
        (∃ y, M.mem y Z.val ∧ φ.toUnarySchema.denote
          (image_env_l (M := lr_model_l native) (N := M) (fun a => a.val.val) ρ) y) →
        Formula.satisfies ρ (.existsE φ.body) := by
  let N := smdl_structure_l I (R := R) model.1.2.1
  let L := lr_model_l native
  have inj : Function.Injective (Subtype.val : N.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have full := smem_full_l I model trans
  obtain ⟨Z,hZ⟩ := ja_value_exists_l S (ZF.models_kpi_l native) α
  have outward := ja_value_image_l (M := N) (N := M) Subtype.val inj full hZ
  refine ⟨Z,⟨ordinal,hZ⟩,fun Y => ⟨fun h => ja_value_unique_l S.val (ZF.models_kpi_l hM) h outward,
    fun eq => eq.symm ▸ outward⟩,?_⟩
  let e : L.Domain → M.Domain := fun a => a.val.val
  have ei : Function.Injective e := fun _ _ eq => Subtype.ext (Subtype.ext eq)
  have ef : ∀ a y, M.mem y (e a) ↔ ∃ b, L.mem b a ∧ e b = y := by
    intro a y
    constructor
    · intro hy
      obtain ⟨b,hb,rfl⟩ := (full a.val y).mp hy
      exact ⟨⟨b,lr_transitive_l native a.property hb⟩,hb,rfl⟩
    · rintro ⟨b,hb,rfl⟩
      exact (full a.val (e b)).mpr ⟨b.val,hb,rfl⟩
  intro n φ ρ truth
  obtain ⟨y,hy,matrix⟩ := truth
  obtain ⟨y₀,hy₀,rfl⟩ := (full Z y).mp hy
  have belongs : Lr_d native y₀ := (lr_iff_l native seed y₀).mpr ⟨α,Z,⟨ordinal,hZ⟩,hy₀⟩
  let y₁ : L.Domain := ⟨y₀,belongs⟩
  apply (Formula.satisfies_exists_iff ρ φ.body).mpr
  refine ⟨y₁,(delta0_image_l (M := L) (N := M) e ei ef φ.delta0 (ρ.push y₁)).mpr ?_⟩
  rw [image_env_push_l]
  exact matrix

/-- 原测试模型的实数基集及其全部相对层，连同对象语言的存在见证上传。 -/
def Lr_upload_d (ω B : (smdl_structure_l I (R := R) model.1.2.1).Domain) : Prop :=
  ∃ S : (smdl_structure_l I (R := R) model.1.2.1).Domain, Lr_seed_d native ω B S ∧
    ∀ α : (smdl_structure_l I (R := R) model.1.2.1).Domain,
      (smdl_structure_l I (R := R) model.1.2.1).IsOrdinal α →
      ∃ Z : (smdl_structure_l I (R := R) model.1.2.1).Domain, Ja_d S α Z ∧
        (∀ Y, Ja_value_d S.val α.val Y ↔ Y = Z.val) ∧
        ∀ {n} (φ : Delta0UnarySchema n) (ρ : Env (lr_model_l native) n),
          (∃ y, M.mem y Z.val ∧ φ.toUnarySchema.denote
            (image_env_l (M := lr_model_l native) (N := M) (fun a => a.val.val) ρ) y) →
          Formula.satisfies ρ (.existsE φ.body)

theorem lr_upload_l {ω B : (smdl_structure_l I (R := R) model.1.2.1).Domain}
    (space : Descriptive.Baire_d (kp_pair_l (ZF.modelsKP native)) ω B) :
    Lr_upload_d hM model native ω B := by
  obtain ⟨S,tc⟩ := ZF.tc_exists_l (kp_pair_l (ZF.modelsKP native)) native B
  exact ⟨S,⟨space,tc⟩,fun α ordinal => lr_layer_upload_l hM model trans native ⟨space,tc⟩ ordinal⟩

end YesMetaZFC.SetTheory.InnerModel.Relative

/-! ## 函数实数族传递种子的有限层刻画

非空的 D→D 函数族在 D 传递时，TC({B}) 由 B、两次并及 D 明确给出。
成员方程可写为 Δ₀ 检查，供弱见证准确识别真实相对 Jensen 起层。
-/
namespace YesMetaZFC.SetTheory.InnerModel.Relative
open Definitional.Project
universe u
variable {M : Structure.{u}}

/-- 两次并与原函数源给出真实最小传递种子；不消费集合论模式。 -/
theorem rf_seed_l {D B U V S : M.Domain} (trans : M.TransitiveSet D)
    (reals : ∀ x, M.mem x B → Fn0_d D D x) (ne : ∃ x, M.mem x B)
    (un : ∀ x, M.mem x U ↔ ∃ y, M.mem y B ∧ M.mem x y)
    (un' : ∀ x, M.mem x V ↔ ∃ y, M.mem y U ∧ M.mem x y)
    (seed : ∀ x, M.mem x S ↔ x = B ∨ M.mem x B ∨ M.mem x U ∨ M.mem x V ∨ M.mem x D) : Tc_d B S := by
  have below {x y} (hx : M.mem x V) (hy : M.mem y x) : M.mem y D := by
    obtain ⟨p,hp,xp⟩ := (un' x).mp hx
    obtain ⟨r,hr,pr⟩ := (un p).mp hp
    obtain ⟨a,ha,b,hb,pair⟩ := (reals r hr).1 p pr
    exact ((kpair_union_l M pair y).mp ⟨x,xp,hy⟩).elim (fun eq => eq ▸ ha) (fun eq => eq ▸ hb)
  refine ⟨?_,(seed B).mpr (Or.inl rfl),?_⟩
  · intro x hx y hy
    apply (seed y).mpr
    rcases (seed x).mp hx with rfl | hx | hx | hx | hx
    · exact Or.inr (Or.inl hy)
    · exact Or.inr (Or.inr (Or.inl ((un y).mpr ⟨x,hx,hy⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ((un' y).mpr ⟨x,hx,hy⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (below hx hy))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (trans x hx y hy))))
  · intro A hA hB x hx
    have bsub y (hy : M.mem y B) := hA B hB y hy
    have usub y (hy : M.mem y U) : M.mem y A := by
      obtain ⟨r,hr,yr⟩ := (un y).mp hy
      exact hA r (bsub r hr) y yr
    have vsub y (hy : M.mem y V) : M.mem y A := by
      obtain ⟨p,hp,yp⟩ := (un' y).mp hy
      exact hA p (usub p hp) y yp
    rcases (seed x).mp hx with rfl | hx | hx | hx | hx
    · exact hB
    · exact bsub x hx
    · exact usub x hx
    · exact vsub x hx
    · obtain ⟨r,hr⟩ := ne
      obtain ⟨y,_,p,pair,pr⟩ := (reals r hr).2.1 x hx
      obtain ⟨v,vp,xv⟩ := (kpair_union_l M pair x).mpr (Or.inl rfl)
      exact hA v (vsub v ((un' v).mpr ⟨p,(un p).mpr ⟨r,hr,pr⟩,vp⟩)) x xv

theorem rf_seed_exists_l (hM : M.Models KP) (D B : M.Domain) :
    ∃ U V S, (∀ x, M.mem x U ↔ ∃ y, M.mem y B ∧ M.mem x y) ∧
      (∀ x, M.mem x V ↔ ∃ y, M.mem y U ∧ M.mem x y) ∧
      ∀ x, M.mem x S ↔ x = B ∨ M.mem x B ∨ M.mem x U ∨ M.mem x V ∨ M.mem x D := by
  obtain ⟨U,un⟩ := KP.exists_union hM B
  obtain ⟨V,un'⟩ := KP.exists_union hM U
  obtain ⟨W,w⟩ := KP.exists_unionOfTwo hM V D
  obtain ⟨T,t⟩ := KP.exists_unionOfTwo hM U W
  obtain ⟨K,k⟩ := KP.exists_unionOfTwo hM B T
  obtain ⟨S,s⟩ := KP.exists_insert hM K B
  exact ⟨U,V,S,un,un',fun x => by rw [s x,k x,t x,w x]; exact or_comm⟩

def Rf_seed0_d (D B S : M.Domain) : Prop := ∀ x, M.mem x S ↔ x = B ∨ M.mem x B ∨
  (∃ r, M.mem r B ∧ M.mem x r) ∨ (∃ r, M.mem r B ∧ ∃ p, M.mem p r ∧ M.mem x p) ∨ M.mem x D

def rf_seed0_m {d} (D B S : Term d) : Formula 1 d := set[d] ⟪
  ⌜B⌝ₛ ∈ ⌜S⌝ₛ ∧ ⌜B⌝ₛ ⊆ ⌜S⌝ₛ ∧
  (∀ r ∈ ⌜B⌝ₛ, r ⊆ ⌜S⌝ₛ ∧ (∀ p ∈ r, p ⊆ ⌜S⌝ₛ)) ∧ ⌜D⌝ₛ ⊆ ⌜S⌝ₛ ∧
  (∀ x ∈ ⌜S⌝ₛ, x = ⌜B⌝ₛ ∨ x ∈ ⌜B⌝ₛ ∨ (∃ r ∈ ⌜B⌝ₛ, x ∈ r) ∨
    (∃ r ∈ ⌜B⌝ₛ, ∃ p ∈ r, x ∈ p) ∨ x ∈ ⌜D⌝ₛ)⟫
derive_free_closed rf_seed0_m

theorem rf_seed0_delta_l {d} (D B S : Term d) : (rf_seed0_m D B S).IsDelta0 :=
  .conj (.mem _ _) (.conj (.atom _ _ _) (.conj
    (.forallMem _ (.conj (.atom _ _ _) (.forallMem _ (.atom _ _ _))))
    (.conj (.atom _ _ _) (.forallMem _ (.disj (.atom _ _ _) (.disj (.mem _ _)
      (.disj (.existsMem _ (.mem _ _)) (.disj (.existsMem _ (.existsMem _ (.mem _ _))) (.mem _ _)))))))))

theorem rf_seed0_sat_l (hE : Extensional M) {d} (ρ : Env M d) (D B S : Term d) :
    Formula.satisfies ρ (rf_seed0_m D B S) ↔ Rf_seed0_d (D.eval ρ) (B.eval ρ) (S.eval ρ) := by
  simp only [rf_seed0_m,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff,Formula.satisfies_subset_iff,
    Formula.satisfies_forallMem_iff,Formula.satisfies_disj_iff,Formula.satisfies_existsMem_iff,
    Formula.satisfies_extensionalEq_iff_eq hE,Definitional.Term.eval_weaken,Definitional.Term.eval_newest]
  constructor
  · rintro ⟨base,bs,rs,ds,small⟩ x
    refine ⟨small x,fun hx => ?_⟩
    rcases hx with rfl | hx | ⟨r,hr,xr⟩ | ⟨r,hr,p,pr,xp⟩ | hx
    · exact base
    · exact bs x hx
    · exact (rs r hr).1 x xr
    · exact (rs r hr).2 p pr x xp
    · exact ds x hx
  · intro h
    exact ⟨(h _).mpr (Or.inl rfl),fun x hx => (h x).mpr (Or.inr (Or.inl hx)),
      fun r hr => ⟨fun x xr => (h x).mpr (Or.inr (Or.inr (Or.inl ⟨r,hr,xr⟩))),
        fun p pr x xp => (h x).mpr (Or.inr (Or.inr (Or.inr (Or.inl ⟨r,hr,p,pr,xp⟩))))⟩,
      fun x hx => (h x).mpr (Or.inr (Or.inr (Or.inr (Or.inr hx)))),fun x hx => (h x).mp hx⟩

/-- 有限层检查准确等价于原最小传递闭包，背景仅需 KP。 -/
theorem rf_seed0_iff_l (hKP : M.Models KP) {D B S : M.Domain} (trans : M.TransitiveSet D)
    (reals : ∀ x, M.mem x B → Fn0_d D D x) (ne : ∃ x, M.mem x B) : Rf_seed0_d D B S ↔ Tc_d B S := by
  obtain ⟨U,V,T,un,un',seed⟩ := rf_seed_exists_l hKP D B
  have tc := rf_seed_l trans reals ne un un' seed
  have two x : M.mem x V ↔ ∃ r, M.mem r B ∧ ∃ p, M.mem p r ∧ M.mem x p := by
    rw [un' x]
    exact ⟨fun ⟨p,hp,xp⟩ => ((un p).mp hp).elim fun r hr => ⟨r,hr.1,p,hr.2,xp⟩,
      fun ⟨r,hr,p,pr,xp⟩ => ⟨p,(un p).mpr ⟨r,hr,pr⟩,xp⟩⟩
  have shape : Rf_seed0_d D B T := fun x => by rw [seed x,un x,two x]
  constructor
  · intro h
    have eq := hKP.1.eq_of_same_members S T (fun x => (h x).trans (shape x).symm)
    exact eq.symm ▸ tc
  · intro h
    exact (tc_unique_l hKP.1 h tc).symm ▸ shape

end YesMetaZFC.SetTheory.InnerModel.Relative

/-! ## 共同相对层中的原 Σ₁(ℝ) 真值运输

实际共同层将派生模型的每个对象放入测试模型的 L(ℝ)。由背景像直接定义
包含映射，不选择模型或对象；传递性使此映射覆盖每个像集合的全部成员。
因此原 8.3 的见证结构及其任意公式真值一并运输。
-/
namespace YesMetaZFC.SetTheory.InnerModel.Relative
open Definitional.Project Internal
universe u v
variable {M : Structure.{u}} {D : Structure.{v}} {𝒞 : OrderedPairConvention}
  (I : 𝒞.Interpretation M) {c P R : M.Domain} (model : Smem_d I c P R)
  (native : (smdl_structure_l I (R := R) model.1.2.1).Models ZF)

def La_transport_d (hD : D.Models KPi) (S Z : D.Domain)
    (B : (smdl_structure_l I (R := R) model.1.2.1).Domain) (e : D.Domain → M.Domain) : Prop :=
  ∃ b : (la_model_l S hD).Domain, b.val = Z ∧
  ∃ j : (la_model_l S hD).Domain → (lr_model_l native).Domain,
    (j b).val = B ∧ (∀ a, (j a).val.val = e a.val) ∧ Function.Injective j ∧
    (∀ a y, (lr_model_l native).mem y (j a) ↔
      ∃ b, (la_model_l S hD).mem b a ∧ j b = y) ∧
    ∀ {n} (φ : Formula 1 n), φ.FreeClosed →
      ∀ x : Fin n → (la_model_l S hD).Domain,
        Sr_truth_d b φ x → Sr_truth_d (j b) φ (fun i => j (x i))

theorem la_common_transport_l (trans : M.TransitiveSet P) (hD : D.Models KPi)
    {S Z : D.Domain} (s : D.TransitiveSet S) (z : La_d S Z)
    {ω B T : (smdl_structure_l I (R := R) model.1.2.1).Domain}
    (seed : Lr_seed_d native ω B T)
    (e : D.Domain → M.Domain) (ei : Function.Injective e)
    (ef : ∀ a y, M.mem y (e a) ↔ ∃ b, D.mem b a ∧ e b = y)
    (real : e Z = B.val)
    (layers : ∀ ξ, D.IsOrdinal ξ →
      ∃ α : (smdl_structure_l I (R := R) model.1.2.1).Domain,
      ∃ W : D.Domain, ∃ W₀ : (smdl_structure_l I (R := R) model.1.2.1).Domain,
        Ja_d S ξ W ∧ Ja_d T α W₀ ∧ e W = W₀.val) :
    La_transport_d I model native hD S Z B e := by
  let N := smdl_structure_l I (R := R) model.1.2.1
  let K := la_model_l S hD
  let L := lr_model_l native
  have nf := smem_full_l I model trans
  -- 对象所在的实际层决定其背景像属于 L(ℝ)，不要求层间初等。
  have image (a : K.Domain) : ∃ b : N.Domain, Lr_d native b ∧ b.val = e a.val := by
    obtain ⟨ξ,U,hu,ha⟩ := a.property
    obtain ⟨α,W,W₀,hw,hw₀,eq⟩ := layers ξ hu.1
    have same : U = W := ja_value_unique_l S hD hu.2 hw.2
    have out : M.mem (e a.val) W₀.val := eq ▸ (ef W (e a.val)).mpr ⟨a.val,same ▸ ha,rfl⟩
    obtain ⟨b,hb,eb⟩ := (nf W₀ (e a.val)).mp out
    exact ⟨b,(lr_iff_l native seed b).mpr ⟨α,W₀,hw₀,hb⟩,eb⟩
  have inside (a : K.Domain) : M.mem (e a.val) P :=
    (image a).elim fun b hb => hb.2 ▸ b.property
  have belongs (a : K.Domain) : Lr_d native (⟨e a.val,inside a⟩ : N.Domain) := by
    obtain ⟨b,hb,eq⟩ := image a
    exact (show b = ⟨e a.val,inside a⟩ from Subtype.ext eq) ▸ hb
  let j : K.Domain → L.Domain := fun a => ⟨⟨e a.val,inside a⟩,belongs a⟩
  have ji : Function.Injective j := fun a b eq =>
    Subtype.ext (ei (congrArg (fun z : L.Domain => z.val.val) eq))
  have jf (a : K.Domain) (y : L.Domain) : L.mem y (j a) ↔ ∃ b, K.mem b a ∧ j b = y := by
    constructor
    · intro hy
      have hy' : M.mem y.val.val (e a.val) := (smem_member_l I model.1 model.2 y.val (j a).val).mp hy
      obtain ⟨b,hb,eq⟩ := (ef a.val y.val.val).mp hy'
      exact ⟨⟨b,la_transitive_l S hD s a.property hb⟩,hb,Subtype.ext (Subtype.ext eq)⟩
    · rintro ⟨b,hb,rfl⟩
      exact (smem_member_l I model.1 model.2 (j b).val (j a).val).mpr
        ((ef a.val (e b.val)).mpr ⟨b.val,hb,rfl⟩)
  exact ⟨⟨Z,z⟩,rfl,j,Subtype.ext real,fun _ => rfl,ji,jf,
    fun _ hc _ truth => truth.image_l j ji jf hc⟩

end YesMetaZFC.SetTheory.InnerModel.Relative

/-! ## 派生模型的原 Σ₁(ℝ) 断言及共同层出口

原一阶公式量化真实传递种子及层中见证集合。满足关系逐项对应
L(ℝ*) 成员结构中的原 8.3 断言，因此同一公式可以进入力迫和初等运输。
-/
namespace YesMetaZFC.SetTheory.InnerModel.Relative
open Definitional.Project Internal
universe u v
variable {M : Structure.{u}}

def Dr_truth_d {n} (B : M.Domain) (φ : Formula 1 n) (x : Fin n → M.Domain) : Prop :=
  (∀ i, M.mem (x i) B) ∧ ∃ S, Tc_d B S ∧ ∃ Q, La_d S Q ∧ M.MemberSubset B Q ∧ St_d Q φ x

def dr_m {n d} (φ : Formula 1 n) (B : Term d) (x : Fin n → Term d) : Formula 1 d :=
  .conj (st_params_m B x) (.existsE (.conj (tc_m B.weaken .newest) (.existsE
    (.conj (la_m (.bound 1) .newest) (.conj (Formula.subset B.weaken.weaken .newest)
      (st_m φ .newest (fun i => (x i).weaken.weaken)))))))

@[simp] theorem dr_closed_l {n d} (φ : Formula 1 n) (hc : φ.FreeClosed)
    (B : Term d) (x : Fin n → Term d) (hb : B.freeSupport = []) (hx : ∀ i, (x i).freeSupport = []) :
    (dr_m φ B x).FreeClosed := by
  simp only [dr_m,Definitional.Formula.FreeClosed]
  exact ⟨st_params_closed_l B x hb hx,tc_m_freeClosed _ _ (by simpa using hb) rfl,
    la_m_freeClosed _ _ rfl rfl,by simpa using hb,st_closed_l φ hc _ _ rfl (fun i => by simpa using hx i)⟩

theorem dr_sat_l (hM : M.Models KP) {n d} (φ : Formula 1 n) (hc : φ.FreeClosed)
    (ρ : Env M d) (B : Term d) (x : Fin n → Term d) :
    Formula.satisfies ρ (dr_m φ B x) ↔ Dr_truth_d (B.eval ρ) φ (fun i => (x i).eval ρ) := by
  simp only [dr_m,Dr_truth_d,Formula.satisfies_conj_iff,Formula.satisfies_exists_iff,
    st_params_sat_l,tc_sat_l,la_sat_l hM,Formula.satisfies_subset_iff,st_sat_l φ hc,
    Definitional.Term.eval_weaken,Definitional.Term.eval_newest]
  rfl

/-- 固定实际种子后，原公式与真实派生模型中的见证断言精确对应。 -/
theorem dr_model_l (hM : M.Models KPi) {B S : M.Domain} (tc : Tc_d B S)
    {n} (φ : Formula 1 n) (hc : φ.FreeClosed) (x : Fin n → M.Domain) :
    Dr_truth_d B φ x ↔
      ∃ b : (la_model_l S hM).Domain, b.val = B ∧
      ∃ y : Fin n → (la_model_l S hM).Domain, (∀ i, (y i).val = x i) ∧ Sr_truth_d b φ y := by
  let D := la_model_l S hM
  have ei : Function.Injective (Subtype.val : D.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have ef (a : D.Domain) (z : M.Domain) : M.mem z a.val ↔ ∃ b : D.Domain, D.mem b a ∧ b.val = z :=
    ⟨fun h => ⟨⟨z,la_transitive_l S hM tc.1 a.property h⟩,h,rfl⟩,fun ⟨_,h,eq⟩ => eq ▸ h⟩
  have inB : La_d S B := la_transitive_l S hM tc.1 (la_seed_l S hM) tc.2.1
  constructor
  · rintro ⟨real,T,tc',Q,hq,sub,sat⟩
    have eq : T = S := tc_unique_l (KPi.models_iff_l.mp hM).1.1 tc' tc
    subst T
    let b : D.Domain := ⟨B,inB⟩
    let q : D.Domain := ⟨Q,hq⟩
    let y : Fin n → D.Domain := fun i => ⟨x i,la_transitive_l S hM tc.1 inB (real i)⟩
    exact ⟨b,rfl,y,fun _ => rfl,real,q,(fun a ha => sub a.val ha),
      (st_image_l (M := D) (N := M) Subtype.val ei ef q φ hc y).mpr sat⟩
  · rintro ⟨b,eq,y,images,truth⟩
    obtain ⟨reals,q,sub,sat⟩ := truth
    refine ⟨fun i => ?_,S,tc,q.val,q.property,?_,?_⟩
    · have hi : M.mem (y i).val b.val := reals i
      simpa only [eq,images] using hi
    · intro a ha
      obtain ⟨a₀,ha₀,rfl⟩ := (ef b a).mp (eq.symm ▸ ha)
      exact sub a₀ ha₀
    · have moved := (st_image_l (M := D) (N := M) Subtype.val ei ef q φ hc y).mp sat
      simpa only [images] using moved

variable {D : Structure.{v}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)
  {c P R : M.Domain} (model : Smem_d I c P R)
  (native : (smdl_structure_l I (R := R) model.1.2.1).Models ZF)

theorem La_transport_d.truth_l {hD : D.Models KPi} {S Z : D.Domain}
    {B : (smdl_structure_l I (R := R) model.1.2.1).Domain} {e : D.Domain → M.Domain}
    (transport : La_transport_d I model native hD S Z B e) (tc : Tc_d Z S)
    {n} {φ : Formula 1 n} (hc : φ.FreeClosed) {x : Fin n → D.Domain}
    (truth : Dr_truth_d Z φ x) :
    ∃ b : (lr_model_l native).Domain, b.val = B ∧
    ∃ y : Fin n → (lr_model_l native).Domain,
      (∀ i, (y i).val.val = e (x i)) ∧ Sr_truth_d b φ y := by
  obtain ⟨b,bZ,j,jB,values,_,_,move⟩ := transport
  obtain ⟨b',bZ',y,images,old⟩ := (dr_model_l hD tc φ hc x).mp truth
  have eq : b' = b := Subtype.ext (bZ'.trans bZ.symm)
  subst b'
  exact ⟨j b,jB,(fun i => j (y i)),fun i => (values (y i)).trans (congrArg e (images i)),move φ hc y old⟩

end YesMetaZFC.SetTheory.InnerModel.Relative
