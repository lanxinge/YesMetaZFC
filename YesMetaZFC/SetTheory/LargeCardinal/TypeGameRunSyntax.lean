import YesMetaZFC.SetTheory.LargeCardinal.TypeGameRunState
import YesMetaZFC.SetTheory.LargeCardinal.IterationTreeSyntax

/-! # 统一历史不变量的原一阶编码 -/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def tg_run_m {d} (ω c₀ o C γ Z A : Term d) (v : Fin 18 → Term d) (u : Fin 46 → Term d) : Formula 1 d := set[d] ⟪
  ⌜ic_model_m⌝ₚ(⌜ω⌝ₛ, ⌜v 2⌝ₛ, ⌜v 3⌝ₛ, ⌜v 0⌝ₛ, ⌜v 1⌝ₛ) ∧
  ⌜tg_context_data_m⌝ₚ(⌜ω⌝ₛ, ⌜v 0⌝ₛ, ⌜v 4⌝ₛ, ⌜v 5⌝ₛ) ∧ ⌜v 7⌝ₛ ∈ ⌜ω⌝ₛ ∧ ⌜KP.succ0_m⌝ₚ(⌜v 6⌝ₛ, ⌜v 7⌝ₛ) ∧
  ⌜it_pnice_m⌝ₚ(⌜ω⌝ₛ, ⌜c₀⌝ₛ, ⌜v 6⌝ₛ, ⌜v 8⌝ₛ, ⌜v 9⌝ₛ, ⌜v 10⌝ₛ, ⌜v 11⌝ₛ, ⌜v 12⌝ₛ) ∧
  ⌜rd_entry0_m⌝ₚ(⌜v 7⌝ₛ, ⌜v 15⌝ₛ, ⌜v 9⌝ₛ) ∧ ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(⌜v 15⌝ₛ, ⌜v 0⌝ₛ, ⌜v 1⌝ₛ) ∧
  ⌜it_map_m⌝ₚ(⌜v 10⌝ₛ, ⌜o⌝ₛ, ⌜v 7⌝ₛ, ⌜v 16⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(⌜C⌝ₛ, ⌜v 5⌝ₛ, ⌜v 16⌝ₛ) ∧
  ⌜tg_anchor_m⌝ₚ(⌜γ⌝ₛ, ⌜Z⌝ₛ, ⌜v 0⌝ₛ, ⌜v 16⌝ₛ) ∧ ⌜rt_record_in_m tg_issued0_m⌝ₚ(⌜v 5⌝ₛ, ⌜v 17⌝ₛ) ∧
  ⌜rt_tuple_m u⌝ₚ(⌜v 17⌝ₛ) ∧ ⌜u 0⌝ₛ = ⌜ω⌝ₛ ∧ ⌜u 6⌝ₛ = ⌜A⌝ₛ ∧ ⌜γ⌝ₛ ⊆ ⌜u 24⌝ₛ ∧
  ⌜tg_past_m⌝ₚ(⌜ω⌝ₛ, ⌜u 19⌝ₛ, ⌜v 13⌝ₛ, ⌜v 0⌝ₛ, ⌜v 14⌝ₛ) ∧ ⌜tg_past_links_m⌝ₚ(⌜v 13⌝ₛ, ⌜v 9⌝ₛ) ∧
  ⌜tg_past_roots_m⌝ₚ(⌜ω⌝ₛ, ⌜v 13⌝ₛ, ⌜v 10⌝ₛ, ⌜o⌝ₛ, ⌜C⌝ₛ, ⌜γ⌝ₛ, ⌜Z⌝ₛ) ∧
  ⌜tg_past_events_m⌝ₚ(⌜ω⌝ₛ, ⌜v 13⌝ₛ, ⌜v 5⌝ₛ, ⌜u 4⌝ₛ, ⌜u 1⌝ₛ, ⌜u 2⌝ₛ, ⌜u 20⌝ₛ) ∧
  ⌜v 14⌝ₛ ∈ ⌜u 24⌝ₛ ∧ (∀ i ν, ⌜rd_entry0_m⌝ₚ(i, ν, ⌜v 12⌝ₛ) → ν ∈ ⌜v 14⌝ₛ ∨ ν = ⌜v 14⌝ₛ) ∧
  ⌜u 19⌝ₛ ∈ ⌜v 6⌝ₛ⟫

@[simp] theorem tg_run_closed_l {d} (ω c₀ o C γ Z A : Term d) (v : Fin 18 → Term d) (u : Fin 46 → Term d)
    (hw : ω.freeSupport = []) (hc : c₀.freeSupport = []) (ho : o.freeSupport = []) (hC : C.freeSupport = [])
    (hγ : γ.freeSupport = []) (hZ : Z.freeSupport = []) (hA : A.freeSupport = [])
    (hv : ∀ i, (v i).freeSupport = []) (hu : ∀ i, (u i).freeSupport = []) : (tg_run_m ω c₀ o C γ Z A v u).FreeClosed := by
  simp -implicitDefEqProofs [tg_run_m, Definitional.Formula.FreeClosed, hw, hc, ho, hC, hγ, hZ, hA, hv, hu,
    rt_record_in_closed_l _ _ _ tg_issued0_closed_l (hv 5) (hv 17), rt_tuple_closed_l u (v 17) hu (hv 17)]

theorem tg_run_sat_l {d} (η : Env M d) (ω c₀ o C γ Z A : Term d) (v : Fin 18 → Term d) (u : Fin 46 → Term d) :
    Formula.satisfies η (tg_run_m ω c₀ o C γ Z A v u) ↔
      Tg_run_d hZF (ω.eval η) (c₀.eval η) (o.eval η) (C.eval η) (γ.eval η) (Z.eval η) (A.eval η)
        (fun i => (v i).eval η) (fun i => (u i).eval η) := by
  simp only [tg_run_m, Formula.satisfies_conj_iff, ic_model_sat_l hZF, tg_context_data_sat_l (ZF.modelsKP hZF),
    Formula.satisfies_mem_iff, KP.succ0_sat_l hZF.1, it_pnice_sat_l hZF, rd_entry0_sat_l hZF.1, smem_sat_l I,
    it_map_sat_l hZF.1, tg_anchor_sat_l (ZF.modelsKP hZF), rt_record_in_sat_l _ _ _ _ tg_issued0_closed_l,
    rt_tuple_sat_l hZF.1, Formula.satisfies_extensionalEq_iff_eq hZF.1, Formula.satisfies_subset_iff,
    tg_past_sat_l hZF, tg_past_links_sat_l I hZF.1, tg_past_roots_sat_l (ZF.modelsKP hZF),
    tg_past_events_sat_l hZF.1, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_disj_iff, Definitional.Term.eval_weaken]
  exact ⟨fun ⟨a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v⟩ => ⟨a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v⟩,
    fun h => ⟨h.source,h.context,h.finite,h.successor,h.tree,h.node,h.model,h.root,h.image,h.anchor,
      h.record,h.values,h.omega,h.alphabet,h.lower,h.past,h.links,h.roots,h.events,h.below,h.bounds,h.span⟩⟩

def Tg_run_code_d (ω c₀ o C γ Z A n s : M.Domain) : Prop := ∃ q : Fin 64 → M.Domain,
  Rt_tuple_d q s ∧ Tg_run_d hZF ω c₀ o C γ Z A (fun i => q (i.castAdd 46)) (fun i => q (Fin.natAdd 18 i)) ∧ q 37 = n

def tg_run_code0_m : Formula 1 9 := rt_exists_m 64
  (.conj (rt_tuple_m (fun i : Fin 64 => .bound (i.castAdd 9)) (.bound 72))
    (.conj (tg_run_m (.bound 64) (.bound 65) (.bound 66) (.bound 67) (.bound 68) (.bound 69) (.bound 70)
      (fun i => .bound ((i.castAdd 46).castAdd 9)) (fun i => .bound ((Fin.natAdd 18 i).castAdd 9)))
      (Formula.extensionalEq (.bound 37) (.bound 71))))

theorem tg_run_code0_closed_l : tg_run_code0_m.FreeClosed := by
  apply (rt_exists_closed_l _).mpr
  refine ⟨rt_tuple_closed_l _ _ (fun _ => rfl) rfl, ?_, ?_⟩
  · apply tg_run_closed_l <;> first | rfl | exact fun _ => rfl
  · exact Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))

theorem tg_run_code0_sat_l (η : Env M 9) : Formula.satisfies η tg_run_code0_m ↔
    Tg_run_code_d hZF (η.bound 0) (η.bound 1) (η.bound 2) (η.bound 3) (η.bound 4) (η.bound 5) (η.bound 6) (η.bound 7) (η.bound 8) := by
  rw [tg_run_code0_m, rt_exists_sat_l]
  apply exists_congr
  intro q
  simp only [Formula.satisfies_conj_iff, rt_tuple_sat_l hZF.1, tg_run_sat_l hZF,
    Formula.satisfies_extensionalEq_iff_eq hZF.1, Term.eval_bound]
  have new (i : Fin 64) : (rt_push_d η 64 q).bound (i.castAdd 9) = q i := rt_push_new_l η q i
  have old (i : Fin 9) : (rt_push_d η 64 q).bound (Fin.natAdd 64 i) = η.bound i := rt_push_old_l η q i
  simp only [new]
  rw [show (rt_push_d η 64 q).bound 72 = η.bound 8 from old 8,
    show (rt_push_d η 64 q).bound 64 = η.bound 0 from old 0,
    show (rt_push_d η 64 q).bound 65 = η.bound 1 from old 1,
    show (rt_push_d η 64 q).bound 66 = η.bound 2 from old 2,
    show (rt_push_d η 64 q).bound 67 = η.bound 3 from old 3,
    show (rt_push_d η 64 q).bound 68 = η.bound 4 from old 4,
    show (rt_push_d η 64 q).bound 69 = η.bound 5 from old 5,
    show (rt_push_d η 64 q).bound 70 = η.bound 6 from old 6,
    show (rt_push_d η 64 q).bound 71 = η.bound 7 from old 7,
    show (rt_push_d η 64 q).bound 37 = q 37 from new 37]

def tg_run_code_m {d} (ω c₀ o C γ Z A n s : Term d) : Formula 1 d :=
  tg_run_code0_m.bind (fun i => [ω,c₀,o,C,γ,Z,A,n,s].get i)

@[simp] theorem tg_run_code_closed_l {d} (ω c₀ o C γ Z A n s : Term d)
    (hw : ω.freeSupport = []) (hc : c₀.freeSupport = []) (ho : o.freeSupport = []) (hC : C.freeSupport = [])
    (hγ : γ.freeSupport = []) (hZ : Z.freeSupport = []) (hA : A.freeSupport = [])
    (hn : n.freeSupport = []) (hs : s.freeSupport = []) : (tg_run_code_m ω c₀ o C γ Z A n s).FreeClosed :=
  (Definitional.Formula.freeClosed_bind_iff_of_closed _
    (Fin.cases hw (Fin.cases hc (Fin.cases ho (Fin.cases hC (Fin.cases hγ (Fin.cases hZ
      (Fin.cases hA (Fin.cases hn (Fin.cases hs (fun i => Fin.elim0 i)))))))))) _).mpr tg_run_code0_closed_l

theorem tg_run_code_sat_l {d} (η : Env M d) (ω c₀ o C γ Z A n s : Term d) :
    Formula.satisfies η (tg_run_code_m ω c₀ o C γ Z A n s) ↔
      Tg_run_code_d hZF (ω.eval η) (c₀.eval η) (o.eval η) (C.eval η) (γ.eval η) (Z.eval η) (A.eval η) (n.eval η) (s.eval η) := by
  rw [tg_run_code_m, Formula.satisfies_bind, tg_run_code0_sat_l hZF]
  rfl

end YesMetaZFC.SetTheory.LargeCardinal
