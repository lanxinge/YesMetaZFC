import YesMetaZFC.SetTheory.LargeCardinal.TypeGameRunNext
import YesMetaZFC.SetTheory.RelationChain

/-! # 有限树的全部旧列与旧前驱保持

两次实际扩张给出六列的包含；树序还保留每个旧终点的全部前驱。
该关系在对象语言中可定义，故可沿内部 ω 传播到任意两个阶段。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Tg_tree_keep_d (v w : Fin 64 → M.Domain) : Prop :=
  M.MemberSubset (v 6) (w 6) ∧
  (∀ i j, M.mem j (v 6) → (Rd_entry_d i j (w 8) ↔ Rd_entry_d i j (v 8))) ∧
  (∀ a : Fin 6, M.MemberSubset (v ⟨8+a.val, by omega⟩) (w ⟨8+a.val, by omega⟩)) ∧
  ∀ i, Rd_entry_d i (v 7) (v 8) → Rd_entry_d i (w 7) (w 8)

def tg_tree_keep_m {d} (v w : Fin 64 → Term d) : Formula 1 d := set[d] ⟪
  ⌜v 6⌝ₛ ⊆ ⌜w 6⌝ₛ ∧
  (∀ i j, j ∈ ⌜v 6⌝ₛ → (⌜rd_entry0_m⌝ₚ(i, j, ⌜w 8⌝ₛ) ↔ ⌜rd_entry0_m⌝ₚ(i, j, ⌜v 8⌝ₛ))) ∧
  (⌜v 8⌝ₛ ⊆ ⌜w 8⌝ₛ ∧ ⌜v 9⌝ₛ ⊆ ⌜w 9⌝ₛ ∧ ⌜v 10⌝ₛ ⊆ ⌜w 10⌝ₛ ∧
    ⌜v 11⌝ₛ ⊆ ⌜w 11⌝ₛ ∧ ⌜v 12⌝ₛ ⊆ ⌜w 12⌝ₛ ∧ ⌜v 13⌝ₛ ⊆ ⌜w 13⌝ₛ) ∧
  (∀ i, ⌜rd_entry0_m⌝ₚ(i, ⌜v 7⌝ₛ, ⌜v 8⌝ₛ) → ⌜rd_entry0_m⌝ₚ(i, ⌜w 7⌝ₛ, ⌜w 8⌝ₛ))⟫

@[simp] theorem tg_tree_keep_closed_l {d} (v w : Fin 64 → Term d)
    (hv : ∀ i, (v i).freeSupport = []) (hw : ∀ i, (w i).freeSupport = []) : (tg_tree_keep_m v w).FreeClosed := by
  simp -implicitDefEqProofs [tg_tree_keep_m, Definitional.Formula.FreeClosed, hv, hw]

theorem tg_tree_keep_sat_l (hE : Extensional M) {d} (η : Env M d) (v w : Fin 64 → Term d) :
    Formula.satisfies η (tg_tree_keep_m v w) ↔ Tg_tree_keep_d (fun i => (v i).eval η) (fun i => (w i).eval η) := by
  simp only [tg_tree_keep_m, Tg_tree_keep_d, Formula.satisfies_conj_iff, Formula.satisfies_subset_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_iff_iff, rd_entry0_sat_l hE, Definitional.Term.eval_weaken,
    Fin.forall_fin_succ, Fin.forall_fin_zero, and_true]
  rfl

def Tg_run_keep_d (s t : M.Domain) : Prop := ∃ v w : Fin 64 → M.Domain,
  Rt_tuple_d v s ∧ Rt_tuple_d w t ∧ Tg_tree_keep_d v w

private def tg_run_keep_body_m : Formula 1 130 :=
  (.conj (rt_tuple_m (fun i : Fin 64 => .bound ((i.castAdd 64).castAdd 2)) (.bound 128))
    (.conj (rt_tuple_m (fun i : Fin 64 => .bound ((Fin.natAdd 64 i).castAdd 2)) (.bound 129))
      (tg_tree_keep_m (fun i => .bound ((i.castAdd 64).castAdd 2))
        (fun i => .bound ((Fin.natAdd 64 i).castAdd 2)))))

def tg_run_keep0_m : Formula 1 2 := rt_exists_m 128 tg_run_keep_body_m

theorem tg_run_keep0_closed_l : tg_run_keep0_m.FreeClosed := by
  apply (rt_exists_closed_l _).mpr
  exact ⟨rt_tuple_closed_l _ _ (fun _ => rfl) rfl, rt_tuple_closed_l _ _ (fun _ => rfl) rfl,
    tg_tree_keep_closed_l _ _ (fun _ => rfl) (fun _ => rfl)⟩

theorem tg_run_keep0_sat_l (hE : Extensional M) (η : Env M 2) :
    Formula.satisfies η tg_run_keep0_m ↔ Tg_run_keep_d (η.bound 0) (η.bound 1) := by
  rw [tg_run_keep0_m, rt_exists_sat_l]
  have read (q : Fin 128 → M.Domain) :
      Formula.satisfies (rt_push_d η 128 q) tg_run_keep_body_m ↔
        Rt_tuple_d (fun i : Fin 64 => q (i.castAdd 64)) (η.bound 0) ∧
        Rt_tuple_d (fun i : Fin 64 => q (Fin.natAdd 64 i)) (η.bound 1) ∧
        Tg_tree_keep_d (fun i => q (i.castAdd 64)) (fun i => q (Fin.natAdd 64 i)) := by
    have new (i : Fin 128) : (rt_push_d η 128 q).bound (i.castAdd 2) = q i := rt_push_new_l η q i
    simp only [tg_run_keep_body_m, Formula.satisfies_conj_iff, rt_tuple_sat_l hE, tg_tree_keep_sat_l hE,
      Term.eval_bound, new]
    rw [show (rt_push_d η 128 q).bound 128 = η.bound 0 from rt_push_old_l η q 0,
      show (rt_push_d η 128 q).bound 129 = η.bound 1 from rt_push_old_l η q 1]
  constructor
  · rintro ⟨q, h⟩
    exact ⟨_, _, (read q).mp h⟩
  · rintro ⟨v, w, h⟩
    let q : Fin 128 → M.Domain := Fin.addCases (motive := fun _ => M.Domain) v w
    refine ⟨q, (read q).mpr ?_⟩
    simpa only [q, Fin.addCases_left, Fin.addCases_right] using h

def tg_run_keep_m {d} (s t : Term d) : Formula 1 d := tg_run_keep0_m.bind (Fin.cases s (fun _ => t))
@[simp] theorem tg_run_keep_closed_l {d} (s t : Term d) (hs : s.freeSupport = []) (ht : t.freeSupport = []) :
    (tg_run_keep_m s t).FreeClosed :=
  (Definitional.Formula.freeClosed_bind_iff_of_closed _ (Fin.cases hs (fun _ => ht)) _).mpr tg_run_keep0_closed_l

theorem tg_run_keep_sat_l (hE : Extensional M) {d} (η : Env M d) (s t : Term d) :
    Formula.satisfies η (tg_run_keep_m s t) ↔ Tg_run_keep_d (s.eval η) (t.eval η) := by
  rw [tg_run_keep_m, Formula.satisfies_bind, tg_run_keep0_sat_l hE]
  rfl

theorem Tg_tree_keep_d.refl_l (v : Fin 64 → M.Domain) : Tg_tree_keep_d v v :=
  ⟨fun _ h => h, fun _ _ _ => Iff.rfl, fun _ _ h => h, fun _ h => h⟩

theorem Tg_tree_keep_d.trans_l {v w z : Fin 64 → M.Domain} (h : Tg_tree_keep_d v w) (g : Tg_tree_keep_d w z) :
    Tg_tree_keep_d v z := ⟨fun x hx => g.1 x (h.1 x hx),
  fun i j hj => (g.2.1 i j (h.1 j hj)).trans (h.2.1 i j hj),
  fun a x hx => g.2.2.1 a x (h.2.2.1 a x hx), fun i hi => g.2.2.2 i (h.2.2.2 i hi)⟩

theorem Tg_run_keep_d.trans_l {s t u : M.Domain} (h : Tg_run_keep_d s t) (g : Tg_run_keep_d t u) : Tg_run_keep_d s u := by
  obtain ⟨v, w, vs, wt, h⟩ := h
  obtain ⟨w', z, wt', zu, g⟩ := g
  have eq := rt_tuple_inj_l wt' wt
  subst w'
  exact ⟨v, z, vs, zu, h.trans_l g⟩

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem It_pnice_d.extension_keep_l {ω c α T Q G E L β T' Q' G' E' L' ξ k : M.Domain}
    (h : It_pnice_d hZF ω c α T Q G E L) (g : It_pnice_d hZF ω c β T' Q' G' E' L')
    (e : It_extension_d α ξ k T Q G E β T' Q' G' E') :
    (∀ i j, M.mem j α → (Rd_entry_d i j T' ↔ Rd_entry_d i j T)) ∧
    M.MemberSubset T T' ∧ M.MemberSubset Q Q' ∧ M.MemberSubset G G' ∧ M.MemberSubset E E' ∧ M.MemberSubset L L' := by
  have sub {A B : M.Domain} (rel : ∀ p, M.mem p A → ∃ i j, KPair_d M p i j)
      (keep : ∀ i j, Rd_entry_d i j A → Rd_entry_d i j B) : M.MemberSubset A B := by
    intro p hp
    obtain ⟨i, j, pair⟩ := rel p hp
    obtain ⟨q, qp, hq⟩ := keep i j ⟨p, pair, hp⟩
    exact kpair_unique_l M hZF.1 qp pair ▸ hq
  refine ⟨fun i j hj => (e.2.1 i j).trans ⟨fun h => h.elim id (fun ⟨eq, _⟩ =>
      (KP.mem_irrefl_d (ZF.modelsKP hZF) α (eq ▸ hj)).elim), Or.inl⟩,
    sub h.tree.diagram.order.relation (fun i j hij => (e.2.1 i j).mpr (Or.inl hij)),
    sub h.tree.diagram.model_function.1 e.2.2.1, sub h.tree.diagram.map_function.1 ?_,
    sub h.tree.move_function.1 e.2.2.2.2.1, sub h.function.1 ?_⟩
  · intro r f hr
    obtain ⟨i, j, pair⟩ := h.tree.diagram.order.relation r ((h.tree.diagram.map_domain r).mpr ⟨f, hr⟩)
    have map := (e.2.2.2.1 i j f (h.tree.diagram.order.bound i j ⟨r, pair,
      (h.tree.diagram.map_domain r).mpr ⟨f, hr⟩⟩).2).mpr ⟨r, pair, hr⟩
    obtain ⟨r', pair', hf⟩ := map
    exact kpair_unique_l M hZF.1 pair' pair ▸ hf
  · intro i ρ hi
    obtain ⟨p, κ, F, hp, payload⟩ := (h.levels i ρ).mp hi
    exact (g.levels i ρ).mpr ⟨p, κ, F, e.2.2.2.2.1 i p hp, payload⟩

theorem Tg_run_next_d.keep_l {ω c o C γ Z A : M.Domain} {v w : Fin 64 → M.Domain}
    (h : Tg_run_d hZF ω c o C γ Z A (fun i => v (i.castAdd 46)) (fun i => v (Fin.natAdd 18 i)))
    (g : Tg_run_d hZF ω c o C γ Z A (fun i => w (i.castAdd 46)) (fun i => w (Fin.natAdd 18 i)))
    (step : Tg_run_next_d hZF ω c (fun i => v (i.castAdd 46)) (fun i => v (Fin.natAdd 18 i))
      (fun i => w (i.castAdd 46)) (fun i => w (Fin.natAdd 18 i))) : Tg_tree_keep_d v w := by
  obtain ⟨k, β, T, Q, G, E, L, _, _, mid, e, e', _, _, even, _, _, _, _, past, _⟩ := step
  obtain ⟨order, cols⟩ := h.tree.extension_keep_l hZF mid e
  obtain ⟨order', cols'⟩ := mid.extension_keep_l hZF g.tree e'
  have sub {a b : M.Domain} (s : M.SuccessorOf b a) : M.MemberSubset a b := fun x hx => (s x).mpr (Or.inl hx)
  have keep (a : Fin 5) : M.MemberSubset (v ⟨8+a.val, by omega⟩) (w ⟨8+a.val, by omega⟩) := by
    refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i))))) a <;>
      intro x hx
    · exact cols'.1 x (cols.1 x hx)
    · exact cols'.2.1 x (cols.2.1 x hx)
    · exact cols'.2.2.1 x (cols.2.2.1 x hx)
    · exact cols'.2.2.2.1 x (cols.2.2.2.1 x hx)
    · exact cols'.2.2.2.2 x (cols.2.2.2.2 x hx)
  refine ⟨fun x hx => sub e'.1 x (sub e.1 x hx),
    fun i j hj => (order' i j (sub e.1 j hj)).trans (order i j hj),
    fun a => Fin.lastCases past (fun i => by simpa only [Fin.val_castSucc] using keep i) a, ?_⟩
  intro i hi
  have old := (e'.2.1 i (v 7)).mpr (Or.inl ((e.2.1 i (v 7)).mpr (Or.inl hi)))
  exact g.tree.tree.diagram.order.trans i (v 7) (w 7) old (g.tree.tree.diagram.map_bound_l hZF even)

end YesMetaZFC.SetTheory.LargeCardinal
