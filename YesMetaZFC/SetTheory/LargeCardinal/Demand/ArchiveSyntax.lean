import YesMetaZFC.SetTheory.LargeCardinal.Demand.Depth
import YesMetaZFC.SetTheory.LargeCardinal.Demand.ArchiveUpdate
import YesMetaZFC.SetTheory.LargeCardinal.Game.RawRootSyntax
import YesMetaZFC.Model.SetTheory.Relations.CollectCode

/-! # 奇深度表和完整字母枚举的可分离公式 -/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M) (hE : Extensional M)

def td_enum_m {d} (Ω X R U E : Term d) : Formula 1 d := set[d] ⟪
  ⌜fn0_m⌝ₚ(⌜Ω⌝ₛ,⌜X⌝ₛ,⌜E⌝ₛ) ∧
  (∀ n x, ⌜rd_entry0_m⌝ₚ(n,x,⌜E⌝ₛ) → ⌜rd_entry0_m⌝ₚ(x,⌜U⌝ₛ,⌜R⌝ₛ)) ∧
  (∀ x, x ∈ ⌜X⌝ₛ → ⌜rd_entry0_m⌝ₚ(x,⌜U⌝ₛ,⌜R⌝ₛ) →
    ∃ n, n ∈ ⌜Ω⌝ₛ ∧ ⌜rd_entry0_m⌝ₚ(n,x,⌜E⌝ₛ))⟫
derive_free_closed td_enum_m

theorem td_enum_sat_l (hE : Extensional M) {d} (ρ : Env M d) (Ω X R U E : Term d) :
    Formula.satisfies ρ (td_enum_m Ω X R U E) ↔
      Td_enum_d (Ω.eval ρ) (X.eval ρ) (R.eval ρ) (U.eval ρ) (E.eval ρ) := by
  simp only [td_enum_m,Formula.satisfies_conj_iff,fn0_sat_l hE,Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff,rd_entry0_sat_l hE,Formula.satisfies_mem_iff,
    Formula.satisfies_exists_iff,Definitional.Term.eval_weaken]
  exact ⟨fun ⟨a,b,c⟩ => ⟨a,b,c⟩,fun h => ⟨h.function,h.letters,h.onto⟩⟩

def td_depth_m {n} (Ω X R U d F : Term n) : Formula 1 n := set[n] ⟪⌜d⌝ₛ ∈ ⌜Ω⌝ₛ ∧
  (∃ D, ⌜Formula.isCartesianProduct kpair_convention_l⌝ₚ(D,⌜d⌝ₛ,⌜Ω⌝ₛ) ∧ ⌜fn0_m⌝ₚ(D,⌜X⌝ₛ,⌜F⌝ₛ)) ∧
  (∀ p x, ⌜rd_entry0_m⌝ₚ(p,x,⌜F⌝ₛ) → ⌜rd_entry0_m⌝ₚ(x,⌜U⌝ₛ,⌜R⌝ₛ))⟫
derive_free_closed td_depth_m

theorem td_depth_sat_l (hE : Extensional M) {n} (ρ : Env M n) (Ω X R U d F : Term n) :
    Formula.satisfies ρ (td_depth_m Ω X R U d F) ↔
      Td_depth_d I (Ω.eval ρ) (X.eval ρ) (R.eval ρ) (U.eval ρ) (d.eval ρ) (F.eval ρ) := by
  simp only [td_depth_m,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff,
    Formula.satisfies_exists_iff,Formula.satisfies_isCartesianProduct_iff I,fn0_sat_l hE,
    Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,rd_entry0_sat_l hE,Definitional.Term.eval_weaken]
  exact ⟨fun ⟨a,b,c⟩ => ⟨a,b,c⟩,fun h => ⟨h.natural,h.table,h.letters⟩⟩

def td_pick_m {n} (Ω d F z : Term n) : Formula 1 n := set[n] ⟪∀ m i e p,
  ⌜KP.succ0_m⌝ₚ(⌜d⌝ₛ,m) → i ∈ ⌜Ω⌝ₛ → e ∈ ⌜Ω⌝ₛ →
    ⌜oc_pair_m (𝒞 := kpair_convention_l)⌝ₚ(i,e,m) → ⌜kpair0_m⌝ₚ(p,i,e) → ⌜rd_entry0_m⌝ₚ(p,⌜z⌝ₛ,⌜F⌝ₛ)⟫
derive_free_closed td_pick_m

theorem td_pick_sat_l (hE : Extensional M) {n} (ρ : Env M n) (Ω d F z : Term n) :
    Formula.satisfies ρ (td_pick_m Ω d F z) ↔ Td_pick_d I (Ω.eval ρ) (d.eval ρ) (F.eval ρ) (z.eval ρ) := by
  simp only [td_pick_m,Td_pick_d,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
    KP.succ0_sat_l hE,Formula.satisfies_mem_iff,oc_pair_sat_l I hE,kpair0_sat_l hE,
    rd_entry0_sat_l hE,Definitional.Term.eval_weaken]
  rfl

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## demanding 档案的完整一阶表示

只量化实际七十三项行码。源计数、完整枚举、深度调度及当前共同图均保留，
使内部归纳和类响应闭包使用与原回合工厂相同的档案性质。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Td_archive_row_d.from_values_d {α : Type u} (v : Fin 73 → α) : Td_archive_row_d α :=
  ⟨fun i => v (i.castAdd 11),v 62,v 63,v 64,v 65,v 66,v 67,v 68,v 69,v 70,v 71,v 72⟩

@[simp] theorem Td_archive_row_d.values_from_l {α : Type u} (v : Fin 73 → α) :
    (Td_archive_row_d.from_values_d v).values_d = v := by
  funext i
  refine Fin.addCases (m := 62) (n := 11) ?_ ?_ i
  · intro i
    exact Fin.addCases_left i
  · intro i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (fun j => Fin.elim0 j))))))))))) i

theorem Td_archive_row_d.from_values_l {α : Type u} (s : Td_archive_row_d α) :
    Td_archive_row_d.from_values_d s.values_d = s := by
  have eq : (Td_archive_row_d.from_values_d s.values_d).v = s.v := by
    funext i
    simp only [Td_archive_row_d.from_values_d,Td_archive_row_d.values_d,Fin.addCases_left]
  cases s
  simp only [Td_archive_row_d.from_values_d,Td_archive_row_d.values_d] at eq ⊢
  congr 1

def td_code_raw_m {d} (X R S δ : Term d) : Formula 1 d :=
  rr_truth_m (𝒞 := kpair_convention_l) (td_code_m (.bound 0) (.bound 1)) X R
    (Fin.cases S (fun _ : Fin 1 => δ))

@[simp] theorem td_code_raw_closed_l {d} (X R S δ : Term d)
    (hx : X.freeSupport = []) (hr : R.freeSupport = []) (hs : S.freeSupport = [])
    (hd : δ.freeSupport = []) : (td_code_raw_m X R S δ).FreeClosed :=
  rr_truth_closed_l _ (by simp -implicitDefEqProofs) _ _ _ hx hr (Fin.cases hs (fun _ => hd))

theorem td_code_raw_sat_l (I : kpair_convention_l.Interpretation M) {d} (ρ : Env M d)
    (X R S δ : Term d) : Formula.satisfies ρ (td_code_raw_m X R S δ) ↔
      Td_code_d I (X.eval ρ) (R.eval ρ) (S.eval ρ) (δ.eval ρ) := by
  rw [td_code_raw_m,rr_truth_sat_l I _ _ (by simp -implicitDefEqProofs)]
  have eq : (fun i : Fin 2 => ((Fin.cases S (fun _ : Fin 1 => δ) : Fin 2 → Term d) i).eval ρ) =
      Fin.cases (S.eval ρ) (fun _ => δ.eval ρ) := funext (Fin.cases rfl (fun _ => rfl))
  exact iff_of_eq (congrArg (Rr_truth_d I (X.eval ρ) (R.eval ρ) (td_code_m (.bound 0) (.bound 1))) eq)

-- 固定项：Ω,c₀,X₀,Ar,Sr,D₀。
def td_archive_source_m {d} (g : Fin 6 → Term d) (v : Fin 73 → Term d) : Formula 1 d :=
  let s := Td_archive_row_d.from_values_d v
  .conj (smdl_m (𝒞 := kpair_convention_l) s.c s.X s.R)
    (.conj (smap_m (𝒞 := kpair_convention_l) (g 0) (g 1) s.c (g 2) s.X s.p)
      (.conj (rr_truth_m (𝒞 := kpair_convention_l) td_round0_m s.X s.R s.v)
        (set[d] ⟪⌜rr_layer_m⌝ₚ(⌜g 0⌝ₛ,⌜s.X⌝ₛ,⌜s.R⌝ₛ,⌜s.v 19⌝ₛ,⌜s.z⌝ₛ) ∧
          ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(⌜s.v 0⌝ₛ,⌜s.L⌝ₛ,⌜s.R⌝ₛ) ∧
          (∀ x, x ∈ ⌜s.X⌝ₛ → ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(x,⌜s.U⌝ₛ,⌜s.R⌝ₛ) →
            ⌜rf_small_m (𝒞 := kpair_convention_l)⌝ₚ(⌜s.X⌝ₛ,⌜s.R⌝ₛ,x)) ∧
          ⌜tg_raw_cofinal_m⌝ₚ(⌜s.v 19⌝ₛ,⌜s.X⌝ₛ,⌜s.R⌝ₛ,⌜s.L⌝ₛ) ∧
          ⌜td_depth_m⌝ₚ(⌜g 0⌝ₛ,⌜s.X⌝ₛ,⌜s.R⌝ₛ,⌜s.v 47⌝ₛ,⌜s.depth⌝ₛ,⌜s.ancestors⌝ₛ) ∧
          ⌜td_enum_m⌝ₚ(⌜g 0⌝ₛ,⌜s.X⌝ₛ,⌜s.R⌝ₛ,⌜s.v 47⌝ₛ,⌜s.enumeration⌝ₛ) ∧
          ⌜td_pick_m⌝ₚ(⌜g 0⌝ₛ,⌜s.depth⌝ₛ,⌜s.ancestors⌝ₛ,⌜s.v 49⌝ₛ) ∧
          (∀ a x, a ∈ ⌜g 5⌝ₛ → ⌜rd_entry0_m⌝ₚ(a,x,⌜s.p⌝ₛ) → ⌜rd_entry0_m⌝ₚ(x,⌜s.v 1⌝ₛ,⌜s.R⌝ₛ)) ∧
          ⌜rd_entry0_m⌝ₚ(⌜g 3⌝ₛ,⌜s.v 50⌝ₛ,⌜s.p⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(⌜g 4⌝ₛ,⌜s.v 22⌝ₛ,⌜s.p⌝ₛ) ∧
          ⌜pc_count_m⌝ₚ(⌜g 0⌝ₛ,⌜s.X⌝ₛ,⌜s.R⌝ₛ,⌜s.v 21⌝ₛ) ∧
          ⌜rd_entry0_m⌝ₚ(⌜s.L⌝ₛ,⌜s.v 21⌝ₛ,⌜s.R⌝ₛ) ∧
          ⌜td_code_raw_m⌝ₚ(⌜s.X⌝ₛ,⌜s.R⌝ₛ,⌜s.v 22⌝ₛ,⌜s.v 21⌝ₛ)⟫)))

@[simp] theorem td_archive_source_closed_l {d} (g : Fin 6 → Term d) (v : Fin 73 → Term d)
    (hg : ∀ i, (g i).freeSupport = []) (hv : ∀ i, (v i).freeSupport = []) :
    (td_archive_source_m g v).FreeClosed := by
  simp -implicitDefEqProofs [td_archive_source_m,Td_archive_row_d.from_values_d,
    Definitional.Formula.FreeClosed,hg,hv]
  exact rr_truth_closed_l td_round0_m td_round0_closed_l _ _ _ (hv 64) (hv 65) (fun i => hv (i.castAdd 11))

theorem td_archive_source_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    {d} (ρ : Env M d) (g : Fin 6 → Term d) (v : Fin 73 → Term d) :
    Formula.satisfies ρ (td_archive_source_m g v) ↔
      Td_archive_source_d I ((g 0).eval ρ) ((g 1).eval ρ) ((g 2).eval ρ) ((g 3).eval ρ)
        ((g 4).eval ρ) ((g 5).eval ρ) (Td_archive_row_d.from_values_d (fun i => (v i).eval ρ)) := by
  simp only [td_archive_source_m,Td_archive_row_d.from_values_d,Formula.satisfies_conj_iff,
    smdl_sat_l I,smap_sat_l I hE,rr_truth_sat_l I _ td_round0_m td_round0_closed_l,
    rr_layer_sat_l I hE,rd_entry0_sat_l hE,Formula.satisfies_orderedPairMem_iff I,
    Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
    Formula.satisfies_mem_iff,rf_small_sat_l I,tg_raw_cofinal_sat_l I hE,td_depth_sat_l I hE,
    td_enum_sat_l hE,td_pick_sat_l I hE,pc_count_sat_l I hE,td_code_raw_sat_l I,Definitional.Term.eval_weaken]
  exact ⟨fun ⟨a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p⟩ => ⟨a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p⟩,
    fun h => ⟨h.model,h.origin,h.round,h.numbers,h.below,h.small,h.cofinal,h.depth,h.enumeration,
      h.chosen,h.root_low,h.letters_root,h.tree_root,h.power_count,h.support_below,h.alphabet_code⟩⟩

def td_archive_view_m {d} (v : Fin 62 → Term d) (g N R c e a z h m : Term d) : Formula 1 d :=
  set[d] ⟪∃ n k τ w, ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(⌜m⌝ₛ,n,⌜z⌝ₛ) ∧
    ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(⌜v 25⌝ₛ,k,⌜g⌝ₛ) ∧
    ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(⌜v 0⌝ₛ,τ,⌜g⌝ₛ) ∧
    ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(⌜v 4⌝ₛ,w,⌜g⌝ₛ) ∧
    ⌜fun N R c e a n h k τ w => rr_truth_m (𝒞 := kpair_convention_l) td_trace0_m N R
      (fun i => [c,e,a,n,h,k,τ,w].get i)⌝ₚ(⌜N⌝ₛ,⌜R⌝ₛ,⌜c⌝ₛ,⌜e⌝ₛ,⌜a⌝ₛ,n,⌜h⌝ₛ,k,τ,w) ∧
    (∃ s, ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(⌜v 44⌝ₛ,s,⌜g⌝ₛ) ∧
      ⌜td_play_at_m⌝ₚ(⌜N⌝ₛ,⌜R⌝ₛ,⌜c⌝ₛ,⌜a⌝ₛ,⌜h⌝ₛ,s))⟫

@[simp] theorem td_archive_view_closed_l {d} (v : Fin 62 → Term d) (g N R c e a z h m : Term d)
    (hv : ∀ i, (v i).freeSupport = []) (hg : g.freeSupport = []) (hN : N.freeSupport = [])
    (hR : R.freeSupport = []) (hc : c.freeSupport = []) (he : e.freeSupport = [])
    (ha : a.freeSupport = []) (hz : z.freeSupport = []) (hh : h.freeSupport = []) (hm : m.freeSupport = []) :
    (td_archive_view_m v g N R c e a z h m).FreeClosed := by
  simp -implicitDefEqProofs [td_archive_view_m,Definitional.Formula.FreeClosed,hv,hg,hz,hm]
  constructor
  · apply rr_truth_closed_l td_trace0_m td_trace0_closed_l <;>
      simp [hN,hR,hc,he,ha,hh,Fin.forall_fin_succ]
  · apply td_play_at_closed_l <;> simp -implicitDefEqProofs [hN,hR,hc,ha,hh]

private theorem td_eval_eight_l {d} (ρ : Env M d) (a b c e f g h k : Term d) :
    (fun i : Fin 8 => ([a,b,c,e,f,g,h,k].get i : Term d).eval ρ) =
      (fun i => [a.eval ρ,b.eval ρ,c.eval ρ,e.eval ρ,f.eval ρ,g.eval ρ,h.eval ρ,k.eval ρ].get i) :=
  funext (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
    (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))))))))
theorem td_archive_view_sat_l (I : kpair_convention_l.Interpretation M)
    {d} (ρ : Env M d) (v : Fin 62 → Term d) (g N R c e a z h m : Term d) :
    Formula.satisfies ρ (td_archive_view_m v g N R c e a z h m) ↔
      Td_archive_view_d I (fun i => (v i).eval ρ) (g.eval ρ) (N.eval ρ) (R.eval ρ) (c.eval ρ)
        (e.eval ρ) (a.eval ρ) (z.eval ρ) (h.eval ρ) (m.eval ρ) := by
  simp only [td_archive_view_m,Td_archive_view_d,Td_trace_at_d,Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff,Formula.satisfies_orderedPairMem_iff I,
    rr_truth_sat_l I _ td_trace0_m td_trace0_closed_l,td_play_at_sat_l I,
    td_eval_eight_l,Definitional.Term.eval_weaken]
  apply exists_congr
  intro n
  apply exists_congr
  intro k
  apply exists_congr
  intro τ
  apply exists_congr
  intro w
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  apply and_congr ?_ Iff.rfl
  apply iff_of_eq
  congr 1
  funext i
  match i with
  | ⟨0,_⟩ => simp only [List.get_eq_getElem,List.getElem_cons_zero,Definitional.Term.eval_weaken]
  | ⟨1,_⟩ => simp only [List.get_eq_getElem,List.getElem_cons_zero,List.getElem_cons_succ,Definitional.Term.eval_weaken]
  | ⟨2,_⟩ => simp only [List.get_eq_getElem,List.getElem_cons_zero,List.getElem_cons_succ,Definitional.Term.eval_weaken]
  | ⟨3,_⟩ => rfl
  | ⟨4,_⟩ => simp only [List.get_eq_getElem,List.getElem_cons_zero,List.getElem_cons_succ,Definitional.Term.eval_weaken]
  | ⟨5,_⟩ => rfl
  | ⟨6,_⟩ => rfl
  | ⟨7,_⟩ => rfl

end YesMetaZFC.SetTheory.LargeCardinal
