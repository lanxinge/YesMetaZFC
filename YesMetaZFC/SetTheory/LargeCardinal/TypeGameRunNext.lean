import YesMetaZFC.SetTheory.LargeCardinal.TypeGameRunSyntax

/-! # 实际后继关系及全部控制参数的集合编码 -/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)

def tg_run_next_m {d} (ω c₀ : Term d) (v w : Fin 18 → Term d) (u t : Fin 46 → Term d) : Formula 1 d := set[d] ⟪
  ∃ k β T Q G E L j h,
    ⌜it_pnice_m⌝ₚ(⌜ω⌝ₛ, ⌜c₀⌝ₛ, β, T, Q, G, E, L) ∧
    ⌜it_extension_m⌝ₚ(⌜v 6⌝ₛ, ⌜v 7⌝ₛ, k, ⌜v 8⌝ₛ, ⌜v 9⌝ₛ, ⌜v 10⌝ₛ, ⌜v 11⌝ₛ, β, T, Q, G, E) ∧
    ⌜it_extension_m⌝ₚ(β, ⌜v 6⌝ₛ, ⌜v 7⌝ₛ, T, Q, G, E, ⌜w 6⌝ₛ, ⌜w 8⌝ₛ, ⌜w 9⌝ₛ, ⌜w 10⌝ₛ, ⌜w 11⌝ₛ) ∧
    ⌜w 7⌝ₛ = β ∧ ⌜KP.succ0_m⌝ₚ(⌜t 19⌝ₛ, ⌜u 19⌝ₛ) ∧ ⌜it_map_m⌝ₚ(⌜w 10⌝ₛ, ⌜v 7⌝ₛ, ⌜w 7⌝ₛ, j) ∧
    (⌜rd_entry0_m⌝ₚ(⌜u 0⌝ₛ, ⌜t 0⌝ₛ, j) ∧ ⌜rd_entry0_m⌝ₚ(⌜u 1⌝ₛ, ⌜t 1⌝ₛ, j) ∧
     ⌜rd_entry0_m⌝ₚ(⌜u 2⌝ₛ, ⌜t 2⌝ₛ, j) ∧ ⌜rd_entry0_m⌝ₚ(⌜u 3⌝ₛ, ⌜t 3⌝ₛ, j) ∧
     ⌜rd_entry0_m⌝ₚ(⌜u 4⌝ₛ, ⌜t 4⌝ₛ, j) ∧ ⌜rd_entry0_m⌝ₚ(⌜u 5⌝ₛ, ⌜t 5⌝ₛ, j) ∧
     ⌜rd_entry0_m⌝ₚ(⌜u 6⌝ₛ, ⌜t 6⌝ₛ, j) ∧ ⌜rd_entry0_m⌝ₚ(⌜u 7⌝ₛ, ⌜t 7⌝ₛ, j) ∧
     ⌜rd_entry0_m⌝ₚ(⌜u 8⌝ₛ, ⌜t 8⌝ₛ, j) ∧ ⌜rd_entry0_m⌝ₚ(⌜u 9⌝ₛ, ⌜t 9⌝ₛ, j) ∧
     ⌜rd_entry0_m⌝ₚ(⌜u 10⌝ₛ, ⌜t 10⌝ₛ, j) ∧ ⌜rd_entry0_m⌝ₚ(⌜u 11⌝ₛ, ⌜t 11⌝ₛ, j) ∧
     ⌜rd_entry0_m⌝ₚ(⌜u 12⌝ₛ, ⌜t 12⌝ₛ, j) ∧ ⌜rd_entry0_m⌝ₚ(⌜u 13⌝ₛ, ⌜t 13⌝ₛ, j) ∧
     ⌜rd_entry0_m⌝ₚ(⌜u 14⌝ₛ, ⌜t 14⌝ₛ, j) ∧ ⌜rd_entry0_m⌝ₚ(⌜u 15⌝ₛ, ⌜t 15⌝ₛ, j) ∧
     ⌜rd_entry0_m⌝ₚ(⌜u 16⌝ₛ, ⌜t 16⌝ₛ, j) ∧ ⌜rd_entry0_m⌝ₚ(⌜u 17⌝ₛ, ⌜t 17⌝ₛ, j) ∧
     ⌜rd_entry0_m⌝ₚ(⌜u 18⌝ₛ, ⌜t 18⌝ₛ, j)) ∧ ⌜rd_entry0_m⌝ₚ(⌜u 20⌝ₛ, h, j) ∧ h ⊆ ⌜t 20⌝ₛ ∧
    ¬ (h = ⌜t 20⌝ₛ) ∧ ⌜v 13⌝ₛ ⊆ ⌜w 13⌝ₛ ∧
    (∃ Y R μ K η C L V q S n s g, ⌜tg_past_at_m⌝ₚ(⌜w 13⌝ₛ, ⌜u 19⌝ₛ, ⌜v 6⌝ₛ, Y, R, μ, K, η, C, L, V, q) ∧
      ⌜tg_saved_branch_m⌝ₚ(⌜ω⌝ₛ, V, q, S, n, s, ⌜u 23⌝ₛ, g) ∧
      ⌜tg_odd_m⌝ₚ(⌜ω⌝ₛ, ⌜v 13⌝ₛ, ⌜v 7⌝ₛ, ⌜v 6⌝ₛ, k, G, ⌜u 1⌝ₛ, ⌜u 23⌝ₛ, ⌜u 22⌝ₛ, ⌜u 7⌝ₛ, S, n, s, g))⟫

@[simp] theorem tg_run_next_closed_l {d} (ω c₀ : Term d) (v w : Fin 18 → Term d) (u t : Fin 46 → Term d)
    (hw : ω.freeSupport = []) (hc : c₀.freeSupport = [])
    (hv : ∀ i, (v i).freeSupport = []) (hw' : ∀ i, (w i).freeSupport = [])
    (hu : ∀ i, (u i).freeSupport = []) (ht : ∀ i, (t i).freeSupport = []) : (tg_run_next_m ω c₀ v w u t).FreeClosed := by
  simp -implicitDefEqProofs [tg_run_next_m, Definitional.Formula.FreeClosed, hw, hc, hv, hw', hu, ht]

theorem tg_run_next_sat_l {d} (η : Env M d) (ω c₀ : Term d) (v w : Fin 18 → Term d) (u t : Fin 46 → Term d) :
    Formula.satisfies η (tg_run_next_m ω c₀ v w u t) ↔ Tg_run_next_d hZF (ω.eval η) (c₀.eval η)
      (fun i => (v i).eval η) (fun i => (u i).eval η) (fun i => (w i).eval η) (fun i => (t i).eval η) := by
  simp only [tg_run_next_m, Tg_run_next_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    it_pnice_sat_l hZF, it_extension_sat_l hZF.1, Formula.satisfies_extensionalEq_iff_eq hZF.1,
    KP.succ0_sat_l hZF.1, it_map_sat_l hZF.1, rd_entry0_sat_l hZF.1, Formula.satisfies_subset_iff, tg_past_at_sat_l hZF.1,
    tg_saved_branch_sat_l hZF.1, tg_odd_sat_l hZF.1, Formula.satisfies_neg_iff,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest, Fin.forall_fin_succ, Fin.forall_fin_zero, and_true]
  rfl

def Tg_run_edge_d (ω c₀ s t : M.Domain) : Prop := ∃ q : Fin 128 → M.Domain,
  Rt_tuple_d (fun i : Fin 64 => q (i.castAdd 64)) s ∧ Rt_tuple_d (fun i : Fin 64 => q (Fin.natAdd 64 i)) t ∧
  Tg_run_next_d hZF ω c₀ (fun i => q ((i.castAdd 46).castAdd 64)) (fun i => q ((Fin.natAdd 18 i).castAdd 64))
    (fun i => q (Fin.natAdd 64 (i.castAdd 46))) (fun i => q (Fin.natAdd 64 (Fin.natAdd 18 i)))

def tg_run_edge0_m : Formula 1 4 := rt_exists_m 128
  (.conj (rt_tuple_m (fun i : Fin 64 => .bound ((i.castAdd 64).castAdd 4)) (.bound 130))
    (.conj (rt_tuple_m (fun i : Fin 64 => .bound ((Fin.natAdd 64 i).castAdd 4)) (.bound 131))
      (tg_run_next_m (.bound 128) (.bound 129)
        (fun i => .bound (((i.castAdd 46).castAdd 64).castAdd 4))
        (fun i => .bound ((Fin.natAdd 64 (i.castAdd 46)).castAdd 4))
        (fun i => .bound (((Fin.natAdd 18 i).castAdd 64).castAdd 4))
        (fun i => .bound ((Fin.natAdd 64 (Fin.natAdd 18 i)).castAdd 4)))))

theorem Tg_run_edge_d.read_l {ω c s t : M.Domain} {v w : Fin 64 → M.Domain}
    (edge : Tg_run_edge_d hZF ω c s t) (ps : Rt_tuple_d v s) (pt : Rt_tuple_d w t) :
    Tg_run_next_d hZF ω c (fun i => v (i.castAdd 46)) (fun i => v (Fin.natAdd 18 i))
      (fun i => w (i.castAdd 46)) (fun i => w (Fin.natAdd 18 i)) := by
  obtain ⟨q, ps', pt', step⟩ := edge
  have ev := rt_tuple_inj_l ps' ps
  have ew := rt_tuple_inj_l pt' pt
  exact ev ▸ ew ▸ step

theorem tg_run_edge0_closed_l : tg_run_edge0_m.FreeClosed := by
  apply (rt_exists_closed_l _).mpr
  refine ⟨rt_tuple_closed_l _ _ (fun _ => rfl) rfl, rt_tuple_closed_l _ _ (fun _ => rfl) rfl, ?_⟩
  apply tg_run_next_closed_l <;> first | rfl | exact fun _ => rfl

theorem tg_run_edge0_sat_l (η : Env M 4) : Formula.satisfies η tg_run_edge0_m ↔
    Tg_run_edge_d hZF (η.bound 0) (η.bound 1) (η.bound 2) (η.bound 3) := by
  rw [tg_run_edge0_m, rt_exists_sat_l]
  apply exists_congr
  intro q
  simp only [Formula.satisfies_conj_iff, rt_tuple_sat_l hZF.1, tg_run_next_sat_l hZF, Term.eval_bound]
  have new (i : Fin 128) : (rt_push_d η 128 q).bound (i.castAdd 4) = q i := rt_push_new_l η q i
  have old (i : Fin 4) : (rt_push_d η 128 q).bound (Fin.natAdd 128 i) = η.bound i := rt_push_old_l η q i
  simp only [new]
  rw [show (rt_push_d η 128 q).bound 128 = η.bound 0 from old 0,
    show (rt_push_d η 128 q).bound 129 = η.bound 1 from old 1,
    show (rt_push_d η 128 q).bound 130 = η.bound 2 from old 2,
    show (rt_push_d η 128 q).bound 131 = η.bound 3 from old 3]

def tg_run_edge_m {d} (ω c₀ s t : Term d) : Formula 1 d := tg_run_edge0_m.bind (fun i => [ω,c₀,s,t].get i)

@[simp] theorem tg_run_edge_closed_l {d} (ω c₀ s t : Term d)
    (hw : ω.freeSupport = []) (hc : c₀.freeSupport = []) (hs : s.freeSupport = []) (ht : t.freeSupport = []) :
    (tg_run_edge_m ω c₀ s t).FreeClosed :=
  (Definitional.Formula.freeClosed_bind_iff_of_closed _
    (Fin.cases hw (Fin.cases hc (Fin.cases hs (Fin.cases ht (fun i => Fin.elim0 i))))) _).mpr tg_run_edge0_closed_l

theorem tg_run_edge_sat_l {d} (η : Env M d) (ω c₀ s t : Term d) :
    Formula.satisfies η (tg_run_edge_m ω c₀ s t) ↔ Tg_run_edge_d hZF (ω.eval η) (c₀.eval η) (s.eval η) (t.eval η) := by
  rw [tg_run_edge_m, Formula.satisfies_bind, tg_run_edge0_sat_l hZF]
  rfl

theorem Tg_run_d.pack_l {ω c₀ o C γ Z A : M.Domain} {v : Fin 18 → M.Domain} {u : Fin 46 → M.Domain}
    (h : Tg_run_d hZF ω c₀ o C γ Z A v u) : ∃ s, Tg_run_code_d hZF ω c₀ o C γ Z A (u 19) s := by
  let q : Fin 64 → M.Domain := Fin.addCases (motive := fun _ => M.Domain) v u
  obtain ⟨s, code⟩ := rt_tuple_exists_l (ZF.modelsKP hZF) q
  refine ⟨s, q, code, ?_, rfl⟩
  simpa only [q, Fin.addCases_left, Fin.addCases_right] using h

end YesMetaZFC.SetTheory.LargeCardinal
