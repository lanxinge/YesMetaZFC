import YesMetaZFC.SetTheory.LargeCardinal.TypeGameEvenBranch
import YesMetaZFC.SetTheory.LargeCardinal.IterationWellFounded

/-! # 任何非偶数共尾枝都有共尾的实际奇数回答

一个结点首次进入有限树时只能是新奇数回答或新偶数结点。内部最小阶段
排除旧树结点；分支与偶数枝分开后，剩下的首次出现结点都来自原保存历史。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Tg_odd_node_d (H y : M.Domain) : Prop := ∃ n r t, Rd_entry_d n r H ∧ KPair_d M r y t
def Tg_odd_cofinal_d (ω b H : M.Domain) : Prop := ∀ i, M.mem i ω →
  ∃ j, M.mem j b ∧ (i = j ∨ M.mem i j) ∧ Tg_odd_node_d H j

def Tg_odd_edge_d (ω H T G B y : M.Domain) : Prop := Tg_odd_node_d H y ∧
  ∃ m ξ k e t ℓ Sₑ Y R μ K η C L V q S n a g,
    Tg_past_at_d H m y Y R μ K η C L V q ∧ Tg_saved_branch_d ω V q S n a t g ∧
    Tg_odd_d ω H ξ y k G e t ℓ Sₑ S n a g ∧ It_pred_d T k y ∧ M.mem ξ B

def Tg_odd_tail_d (ω H T G B b : M.Domain) : Prop := ∃ z,
  M.mem z b ∧ ¬ M.mem z B ∧ Tg_odd_node_d H z ∧ ∀ y, M.mem y b → M.mem z y →
    Tg_odd_edge_d ω H T G B y ∧ ∀ k, It_pred_d T k y →
      M.mem k b ∧ ¬ M.mem k B ∧ (z = k ∨ M.mem z k)

private def Tg_stage_has_d (f y k : M.Domain) : Prop := ∃ v : Fin 64 → M.Domain,
  ∃ s, Rd_entry_d k s f ∧ Rt_tuple_d v s ∧ M.mem y (v 6)
private def tg_stage_body_m : Formula 1 67 := .existsE
  (.conj (rd_entry0_m (.bound 67) .newest (.bound 65))
    (.conj (rt_tuple_m (fun i : Fin 64 => .bound (i.castAdd 3).succ) .newest) (.mem (.bound 66) (.bound 7))))
private def tg_stage0_m : Formula 1 3 := rt_exists_m 64 tg_stage_body_m
private theorem tg_stage_closed_l : tg_stage0_m.FreeClosed := by
  apply (rt_exists_closed_l _).mpr
  simp -implicitDefEqProofs [tg_stage_body_m, Definitional.Formula.FreeClosed]
  exact rt_tuple_closed_l _ _ (fun _ => rfl) rfl
private theorem tg_stage_sat_l (hE : Extensional M) (η : Env M 3) :
    Formula.satisfies η tg_stage0_m ↔ Tg_stage_has_d (η.bound 0) (η.bound 1) (η.bound 2) := by
  rw [tg_stage0_m, rt_exists_sat_l]
  apply exists_congr
  intro v
  have new (i : Fin 64) : (rt_push_d η 64 v).bound (i.castAdd 3) = v i := rt_push_new_l η v i
  simp only [tg_stage_body_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    rd_entry0_sat_l hE, rt_tuple_sat_l hE, Formula.satisfies_mem_iff, Term.eval_bound]
  change (∃ s, Rd_entry_d ((rt_push_d η 64 v).bound 66) s ((rt_push_d η 64 v).bound 64) ∧
    Rt_tuple_d (fun j => (rt_push_d η 64 v).bound (j.castAdd 3)) s ∧
    M.mem ((rt_push_d η 64 v).bound 65) ((rt_push_d η 64 v).bound 6)) ↔ _
  simp only [new]
  rw [show (rt_push_d η 64 v).bound 64 = η.bound 0 from rt_push_old_l η v 0,
    show (rt_push_d η 64 v).bound 65 = η.bound 1 from rt_push_old_l η v 1,
    show (rt_push_d η 64 v).bound 66 = η.bound 2 from rt_push_old_l η v 2,
    show (rt_push_d η 64 v).bound 6 = v 6 from new 6]

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_sequence_d.late_odd_l {ω c o C γ Z A D f B e s₀ y : M.Domain} {U : Fin 6 → M.Domain}
    {v₀ : Fin 64 → M.Domain} (h : Tg_sequence_d hZF ω c o C γ Z A D f)
    (tree : It_pnice_d hZF ω c ω (U 0) (U 1) (U 2) (U 3) (U 4))
    (columns : ∀ a x, M.mem x (U a) ↔ Tg_run_value_d ⟨8+a.val, by omega⟩ f x)
    (even : ∀ x, M.mem x B ↔ Tg_even_d f (U 0) x) (empty : ∀ x, ¬ M.mem x e)
    (first : Rd_entry_d e s₀ f) (code₀ : Rt_tuple_d v₀ s₀) (hy : M.mem y ω)
    (outside : ¬ M.mem y (v₀ 6)) (not_even : ¬ M.mem y B) : Tg_odd_edge_d ω (U 5) (U 0) (U 2) B y := by
  classical
  have hw := tree.tree.omega
  let φ : UnarySchema 2 := {
    body := tg_stage0_m.bind (fun i => [.bound 1, .bound 2, .newest].get i)
    freeClosed := (Definitional.Formula.freeClosed_bind_iff_of_closed _
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))) _).mpr tg_stage_closed_l }
  let ε : Env M 2 := ⟨Fin.cases f (fun _ => y), fun _ => y⟩
  have sat k : φ.denote ε k ↔ Tg_stage_has_d f y k := by
    rw [UnarySchema.denote, Formula.satisfies_bind, tg_stage_sat_l hZF.1]; rfl
  obtain ⟨S, ss⟩ := ZF.separation_exists_d hZF φ ε ω
  have stages k : M.mem k S ↔ Tg_stage_has_d f y k := (ss k).trans
    ((and_congr_right fun _ => sat k).trans ⟨And.right, fun q => ⟨by
      obtain ⟨_, s, hs, _⟩ := q; exact (h.function.bound_l hs).1, q⟩⟩)
  obtain ⟨s₁, _, h₁⟩ := h.function.2.1 y hy
  obtain ⟨_, _, v₁, p₁, _⟩ := h.rows y s₁ h₁
  obtain ⟨k, hk, least⟩ := KP.mem_minimal_exists_d (ZF.modelsKP hZF)
    ⟨y, (stages y).mpr ⟨v₁, s₁, h₁, p₁, (h.read_l hZF h₁ p₁).2⟩⟩
  obtain ⟨v, s, hs, code, hyv⟩ := (stages k).mp hk
  have hkω := (h.function.bound_l hs).1
  have nonempty : ∃ x, M.mem x k := by
    apply Classical.byContradiction
    intro no
    have eq := hZF.1.eq_of_same_members k e (fun x => iff_of_false (fun hx => no ⟨x, hx⟩) (empty x))
    subst k
    have eq := (fn0_function_l (ZF.modelsKP hZF) h.function).1.2 e s s₀ hs first
    subst s
    exact outside (congrFun (rt_tuple_inj_l code code₀) 6 ▸ hyv)
  obtain ⟨l, hlω, succ⟩ := hw.exists_predecessor_of_mem_of_nonempty hZF hkω nonempty
  obtain ⟨t, _, ht⟩ := h.function.2.1 l hlω
  obtain ⟨_, _, w, ct, _⟩ := h.rows l t ht
  have old : ¬ M.mem y (w 6) := fun hy => least l ((stages l).mpr ⟨w, t, ht, ct, hy⟩) succ.predecessor_mem
  obtain ⟨a, β, T, Q, G, E, L₀, _, _, mid, ext₁, ext₂, head, _, _, _, _, _, _, _,
    Y, R, μ, K, η, C, L, V, q, S, n, digits, g, saved, br, odd⟩ := (h.steps l k t s succ ht hs).read_l hZF ct code
  rcases (ext₂.1 y).mp hyv with hyβ | eq
  · rcases (ext₁.1 y).mp hyβ with hyold | eq
    · exact (old hyold).elim
    · have eq := hZF.1.eq_of_same_members y (w 6) eq
      subst y
      have oldRun := (h.read_l hZF ht ct).1
      have newRun := (h.read_l hZF hs code).1
      have inside a := fun z hz => (columns a z).mpr ⟨v, k, s, hs, code, hz⟩
      have oldInside a := fun z hz => (columns a z).mpr ⟨w, l, t, ht, ct, hz⟩
      have ha : M.mem a (w 6) := by
        rcases odd with ⟨_, eq, _⟩ | ⟨_, Y, R, μ, K, η, C, L, V, q, _, _, _, _, _, _, _, _, _, row, _⟩
        · exact eq ▸ oldRun.successor.predecessor_mem
        · obtain ⟨d, hd, _⟩ := oldRun.links _ _ _ _ _ _ _ _ _ _ _ row
          exact (oldRun.tree.tree.diagram.model_domain a).mpr ⟨d, hd⟩
      have keep₁ := oldRun.tree.extension_keep_l hZF mid ext₁
      have keep₂ := mid.extension_keep_l hZF newRun.tree ext₂
      have hyβ := ext₁.1.predecessor_mem
      have hyv := (ext₂.1 _).mpr (Or.inl hyβ)
      have hav := (ext₂.1 _).mpr (Or.inl ((ext₁.1 _).mpr (Or.inl ha)))
      have tip i : Rd_entry_d i (w 6) T ↔ i = w 6 ∨ Rd_entry_d i a (w 8) :=
        (ext₁.2.1 i (w 6)).trans ⟨fun h => h.elim
          (fun h => (KP.mem_irrefl_d (ZF.modelsKP hZF) _ (oldRun.tree.tree.diagram.order.bound _ _ h).2).elim)
          And.right, fun h => Or.inr ⟨rfl, h⟩⟩
      have pred : It_pred_d (U 0) a (w 6) := ⟨ha, fun i =>
        (h.order_l hZF hw columns hs code hyv).trans ((keep₂.1 i _ hyβ).trans
          ((tip i).trans (or_congr Iff.rfl ((keep₁.1 i a ha).symm.trans
            ((keep₂.1 i a ((ext₁.1 a).mpr (Or.inl ha))).symm.trans (h.order_l hZF hw columns hs code hav).symm)))))⟩
      have liftMap {i j} (hj : It_map_d G i (w 6) j) : It_map_d (U 2) i (w 6) j := by
        obtain ⟨r, pair, p, pp, hp⟩ := (ext₂.2.2.2.1 i (w 6) j hyβ).mpr hj
        exact ⟨r, pair, p, pp, inside 2 p hp⟩
      have moved : Tg_odd_d ω (U 5) (w 7) (w 6) a (U 2) (w 19) (w 41) (w 40) (w 25) S n digits g := by
        rcases odd with reset | ⟨ne, Y, R, μ, K, η, C, L, V, q, S₀, n₀, s₀, t₀, g₀, j, x, b, z, row, br, hj, rest⟩
        · obtain ⟨he, hk, hg, j, edge, image⟩ := reset
          exact Or.inl ⟨he, hk, hg, j, liftMap edge, image⟩
        · obtain ⟨r, ⟨p, pair, hp⟩, cell⟩ := row
          have hj := (ext₂.2.2.2.1 a (w 6) j hyβ).mpr hj
          obtain ⟨r', pair', p', pp, hp'⟩ := hj
          exact Or.inr ⟨ne, Y, R, μ, K, η, C, L, V, q, S₀, n₀, s₀, t₀, g₀, j, x, b, z,
            ⟨r, ⟨p, pair, oldInside 5 p hp⟩, cell⟩, br, ⟨r', pair', p', pp, inside 2 p' hp'⟩, rest⟩
      obtain ⟨r, ⟨p, pair, hp⟩, cell⟩ := saved
      have row : Tg_past_at_d (U 5) (w 37) (w 6) Y R μ K η C L V q :=
        ⟨r, ⟨p, pair, inside 5 p hp⟩, cell⟩
      exact ⟨⟨w 37, r, cell.choose, ⟨p, pair, inside 5 p hp⟩, cell.choose_spec.1⟩,
        w 37, w 7, a, w 19, w 41, w 40, w 25, Y, R, μ, K, η, C, L, V, q, S, n, digits, g,
        row, br, moved, pred, (even (w 7)).mpr ⟨w, l, t, ht, ct,
          tree.tree.diagram.order.refl (w 7) oldRun.finite⟩⟩
  · have eq := hZF.1.eq_of_same_members y β eq
    have yr : y = v 7 := eq.trans head.symm
    exact (not_even ((even y).mpr ⟨v, k, s, hs, code,
      yr.symm ▸ tree.tree.diagram.order.refl (v 7) (h.read_l hZF hs code).1.finite⟩)).elim

theorem Tg_sequence_d.odd_tail_l {ω c o C γ Z A D f B b : M.Domain} {U : Fin 6 → M.Domain}
    (h : Tg_sequence_d hZF ω c o C γ Z A D f)
    (tree : It_pnice_d hZF ω c ω (U 0) (U 1) (U 2) (U 3) (U 4))
    (columns : ∀ a x, M.mem x (U a) ↔ Tg_run_value_d ⟨8+a.val, by omega⟩ f x)
    (even_branch : It_branch_d ω (U 0) B) (even : ∀ x, M.mem x B ↔ Tg_even_d f (U 0) x)
    (branch : It_branch_d ω (U 0) b) (ne : b ≠ B) :
    Tg_odd_cofinal_d ω b (U 5) ∧ Tg_odd_tail_d ω (U 5) (U 0) (U 2) B b := by
  classical
  have hw := tree.tree.omega
  have ord := hw.isOrdinal hZF
  have ir := KP.mem_irrefl_d (ZF.modelsKP hZF)
  have different : ∃ x, M.mem x b ∧ ¬ M.mem x B := by
    apply Classical.byContradiction
    intro no
    have sub x (hx : M.mem x b) : M.mem x B := Classical.byContradiction (fun h => no ⟨x, hx, h⟩)
    apply ne (hZF.1.eq_of_same_members b B fun x => ⟨sub x, fun hx => ?_⟩)
    obtain ⟨y, hy, le⟩ := branch.cofinal x (even_branch.subset x hx)
    exact branch.down x y (even_branch.forward_l tree.tree.diagram.order hx (sub y hy) le) hy
  obtain ⟨x, hx, hxn⟩ := different
  have upper a d (ha : M.mem a ω) (hd : M.mem d ω) :
      ∃ z, M.mem z ω ∧ M.MemberSubset a z ∧ M.MemberSubset d z := by
    rcases ord.wellOrder.linear.compare a ha d hd with eq | lt | gt
    · exact ⟨d, hd, fun y hy => (eq y).mp hy, fun _ h => h⟩
    · exact ⟨d, hd, (hw.members_areOrdinals hZF d hd).transitive a lt, fun _ h => h⟩
    · exact ⟨a, ha, fun _ h => h, (hw.members_areOrdinals hZF a ha).transitive d gt⟩
  have le {a d} (ha : M.mem a ω) (hd : M.mem d ω) (sub : M.MemberSubset a d) : a = d ∨ M.mem a d := by
    rcases ord.wellOrder.linear.compare a ha d hd with eq | lt | gt
    · exact Or.inl (hZF.1.eq_of_same_members a d eq)
    · exact Or.inr lt
    · exact (ir d (sub d gt)).elim
  obtain ⟨e, empty, he⟩ := hw.1.1
  obtain ⟨s₀, _, first⟩ := h.function.2.1 e he
  obtain ⟨_, _, v₀, code₀, _⟩ := h.rows e s₀ first
  have run := (h.read_l hZF first code₀).1
  have ha := (hw.1.2 _ run.finite).elim fun a h => (h.1.eq hZF.1 run.successor) ▸ h.2
  have late i (hi : M.mem i ω) : ∃ y,
      M.mem y b ∧ (i = y ∨ M.mem i y) ∧ ¬ M.mem y B ∧ ¬ M.mem y (v₀ 6) := by
    obtain ⟨z, hz, az, xz⟩ := upper (v₀ 6) x ha (branch.subset x hx)
    obtain ⟨m, hm, zm, im⟩ := upper z i hz hi
    obtain ⟨y, hy, my⟩ := branch.cofinal m hm
    have mysub : M.MemberSubset m y := my.elim (fun eq => eq ▸ fun _ h => h)
      (fun lt => (hw.members_areOrdinals hZF y (branch.subset y hy)).transitive m lt)
    have iy := le hi (branch.subset y hy) (fun a h => mysub a (im a h))
    have xy := le (branch.subset x hx) (branch.subset y hy) (fun a h => mysub a (zm a (xz a h)))
    exact ⟨y, hy, iy, fun h => hxn (even_branch.down x y
      (branch.forward_l tree.tree.diagram.order hx hy xy) h), fun h => ir y (mysub y (zm y (az y h)))⟩
  refine ⟨fun i hi => ?_, ?_⟩
  · obtain ⟨y, hy, iy, not_even, outside⟩ := late i hi
    exact ⟨y, hy, iy, (h.late_odd_l hZF tree columns even empty first code₀ (branch.subset y hy) outside not_even).1⟩
  · obtain ⟨z, hz, _, not_even, outside⟩ := late e he
    refine ⟨z, hz, not_even,
      (h.late_odd_l hZF tree columns even empty first code₀ (branch.subset z hz) outside not_even).1,
      fun y hy zy => ?_⟩
    have order := branch.forward_l tree.tree.diagram.order hz hy (Or.inr zy)
    have yn : ¬ M.mem y B := fun h => not_even (even_branch.down z y order h)
    have yo : ¬ M.mem y (v₀ 6) := fun h => outside ((hw.members_areOrdinals hZF _ ha).transitive y h z zy)
    refine ⟨h.late_odd_l hZF tree columns even empty first code₀ (branch.subset y hy) yo yn, ?_⟩
    intro k pred
    have zk : Rd_entry_d z k (U 0) := ((pred.2 z).mp order).elim
      (fun eq => (ir y (eq ▸ zy)).elim) id
    have ky := (pred.2 k).mpr (Or.inr (tree.tree.diagram.order.refl k
      (hw.transitive hZF y (branch.subset y hy) k pred.1)))
    exact ⟨branch.down k y ky hy, fun h => not_even (even_branch.down z k zk h),
      tree.tree.diagram.order.forward z k zk⟩

end YesMetaZFC.SetTheory.LargeCardinal
