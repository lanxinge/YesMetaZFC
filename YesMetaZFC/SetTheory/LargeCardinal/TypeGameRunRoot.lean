import YesMetaZFC.SetTheory.LargeCardinal.TypeGameRunUnion

/-! # 原树名称沿统一递归和有限树取并保持 -/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Tg_run_name_d (S s : M.Domain) : Prop := ∃ v : Fin 64 → M.Domain,
  Rt_tuple_d v s ∧ Rd_entry_d S (v 25) (v 16)

def tg_run_name0_m : Formula 1 2 := rt_exists_m 64
  (.conj (rt_tuple_m (fun i => .bound (i.castAdd 2)) (.bound 65))
    (rd_entry0_m (.bound 64) (.bound 25) (.bound 16)))

theorem tg_run_name0_closed_l : tg_run_name0_m.FreeClosed := by
  apply (rt_exists_closed_l _).mpr
  refine ⟨rt_tuple_closed_l _ _ (fun _ => rfl) rfl, ?_⟩
  simp -implicitDefEqProofs [rd_entry0_m]

theorem tg_run_name0_sat_l (hE : Extensional M) (η : Env M 2) :
    Formula.satisfies η tg_run_name0_m ↔ Tg_run_name_d (η.bound 0) (η.bound 1) := by
  rw [tg_run_name0_m, rt_exists_sat_l]
  apply exists_congr
  intro v
  simp only [Formula.satisfies_conj_iff, rt_tuple_sat_l hE, rd_entry0_sat_l hE, Term.eval_bound]
  have new (i : Fin 64) : (rt_push_d η 64 v).bound (i.castAdd 2) = v i := rt_push_new_l η v i
  simp only [new]
  rw [show (rt_push_d η 64 v).bound 65 = η.bound 1 from rt_push_old_l η v 1,
    show (rt_push_d η 64 v).bound 64 = η.bound 0 from rt_push_old_l η v 0]
  rfl

def tg_run_name_m {d} (S s : Term d) : Formula 1 d := tg_run_name0_m.bind (Fin.cases S (fun _ => s))
@[simp] theorem tg_run_name_closed_l {d} (S s : Term d) (hS : S.freeSupport = []) (hs : s.freeSupport = []) :
    (tg_run_name_m S s).FreeClosed :=
  (Definitional.Formula.freeClosed_bind_iff_of_closed _ (Fin.cases hS (fun _ => hs)) _).mpr tg_run_name0_closed_l

theorem tg_run_name_sat_l (hE : Extensional M) {d} (η : Env M d) (S s : Term d) :
    Formula.satisfies η (tg_run_name_m S s) ↔ Tg_run_name_d (S.eval η) (s.eval η) := by
  rw [tg_run_name_m, Formula.satisfies_bind, tg_run_name0_sat_l hE]; rfl

variable (hZF : M.Models ZF)

theorem Tg_run_edge_d.name_l {ω c o C γ Z A n m s t S : M.Domain}
    (h : Tg_run_code_d hZF ω c o C γ Z A n s) (g : Tg_run_code_d hZF ω c o C γ Z A m t)
    (step : Tg_run_edge_d hZF ω c s t) (name : Tg_run_name_d S s) : Tg_run_name_d S t := by
  obtain ⟨v, vs, h, _⟩ := h
  obtain ⟨w, wt, g, _⟩ := g
  obtain ⟨v', vs', image⟩ := name
  have eq := rt_tuple_inj_l vs' vs
  subst v'
  have edge := step.read_l hZF vs wt
  have keep := edge.keep_l hZF h g
  have root : It_map_d (w 10) o (v 7) (v 16) := by
    obtain ⟨r, pair, p, pp, hp⟩ := h.root
    exact ⟨r, pair, p, pp, keep.2.2.1 2 p hp⟩
  obtain ⟨_, _, _, _, _, _, _, j, _, _, _, _, _, _, even, images, _⟩ := edge
  exact ⟨w, wt, g.tree.tree.diagram.comp o (v 7) (w 7) (v 16) j (w 16)
    root even g.root S (v 25) (w 25) image (images 7)⟩

theorem Tg_sequence_d.root_tree_l {ω c o C γ Z A D f S : M.Domain} {U : Fin 6 → M.Domain}
    (h : Tg_sequence_d hZF ω c o C γ Z A D f)
    (columns : ∀ a x, M.mem x (U a) ↔ Tg_run_value_d ⟨8+a.val, by omega⟩ f x)
    (names : ∀ i s, Rd_entry_d i s f → Tg_run_name_d S s) : Tg_root_tree_d ω (U 5) (U 2) o S := by
  intro m i Y R μ K η E L V q S' n digits t g row br
  obtain ⟨r, ⟨p, pair, hp⟩, cell⟩ := row
  obtain ⟨v, k, s, hs, code, hp⟩ := (columns 5 p).mp hp
  have run := (h.read_l hZF hs code).1
  obtain ⟨w, pack, image⟩ := names k s hs
  have eq := rt_tuple_inj_l pack code
  subst w
  obtain ⟨S₀, image₀, trees⟩ := run.tree_name
  have diagram := run.tree.tree.diagram
  obtain ⟨a, B, T, ha, ma⟩ := diagram.model_l hZF (diagram.order.bound o (v 7) (diagram.map_bound_l hZF run.root)).1
  have map := diagram.elementary o (v 7) (v 16) a B T (v 15) (v 0) (v 1) run.root ha run.node ma run.model.1
  have eq := map.1.2 S₀ S (v 25) image₀ image
  subst S₀
  obtain ⟨j, ⟨a, ap, b, bp, hb⟩, value⟩ := trees m i Y R μ K η E L V q S' n digits t g ⟨r, ⟨p, pair, hp⟩, cell⟩ br
  exact ⟨j, ⟨a, ap, b, bp, (columns 2 b).mpr ⟨v, k, s, hs, code, hb⟩⟩, value⟩

end YesMetaZFC.SetTheory.LargeCardinal
