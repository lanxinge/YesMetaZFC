import YesMetaZFC.SetTheory.LargeCardinal.Demand.ArchiveSyntax
import YesMetaZFC.SetTheory.LargeCardinal.Demand.ArchiveUpdate

/-! # 档案函数及原树对应的对象语言

行码唯一性保证对象量词读取的仍是原工厂登记的同一行。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

-- Ω,c₀,X₀,Ar,Sr,N,R,χ,c,e,a,z,h,m,r,D₀,q。
private def td_archive_entry_body_m {d} (g : Fin 17 → Term d) (v : Fin 73 → Term d) : Formula 1 d :=
  let s := Td_archive_row_d.from_values_d v
  .conj (rt_tuple_m v (g 14))
    (.conj (td_archive_source_m (fun i => [g 0,g 1,g 2,g 3,g 4,g 15].get i) v)
      (set[d] ⟪∃ l V Δ t,
        ⌜ic_common_m⌝ₚ(⌜s.X⌝ₛ,⌜s.R⌝ₛ,⌜g 5⌝ₛ,⌜g 6⌝ₛ,⌜s.L⌝ₛ,l,⌜s.U⌝ₛ,V,Δ,t) ∧
        (⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(l,⌜g 7⌝ₛ,⌜g 6⌝ₛ) ∨ l = ⌜g 7⌝ₛ) ∧
        ⌜tg_root_square_m⌝ₚ(⌜g 15⌝ₛ,⌜s.p⌝ₛ,⌜g 16⌝ₛ,t) ∧
        ⌜fun t N R c e a z h m => td_archive_view_m (fun i => (s.v i).weaken.weaken.weaken.weaken)
          t N R c e a z h m⌝ₚ(t,⌜g 5⌝ₛ,⌜g 6⌝ₛ,⌜g 8⌝ₛ,⌜g 9⌝ₛ,⌜g 10⌝ₛ,⌜g 11⌝ₛ,⌜g 12⌝ₛ,⌜g 13⌝ₛ)⟫))

def td_archive_entry_m {d} (g : Fin 17 → Term d) : Formula 1 d := rb_exists_m
  (td_archive_entry_body_m (fun i => (g i).rename (Fin.natAdd 73)) (fun i => .bound (i.castAdd d)))

@[simp] theorem td_archive_entry_closed_l {d} (g : Fin 17 → Term d)
    (hg : ∀ i, (g i).freeSupport = []) : (td_archive_entry_m g).FreeClosed := by
  simp -implicitDefEqProofs [td_archive_entry_m,td_archive_entry_body_m,Td_archive_row_d.from_values_d,
    Definitional.Formula.FreeClosed,hg,Fin.forall_fin_succ]
  exact rt_tuple_closed_l _ _ (fun _ => rfl) (by simpa using hg 14)

theorem td_archive_entry_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (g : Fin 17 → Term d) :
    Formula.satisfies ρ (td_archive_entry_m g) ↔
      Td_archive_entry_d (kp_pair_l hKP) ((g 0).eval ρ) ((g 1).eval ρ) ((g 2).eval ρ)
        ((g 3).eval ρ) ((g 4).eval ρ) ((g 5).eval ρ) ((g 6).eval ρ) ((g 7).eval ρ)
        ((g 8).eval ρ) ((g 9).eval ρ) ((g 10).eval ρ) ((g 11).eval ρ) ((g 12).eval ρ)
        ((g 13).eval ρ) ((g 14).eval ρ) ((g 15).eval ρ) ((g 16).eval ρ) := by
  simp only [td_archive_entry_m,td_archive_entry_body_m,rb_exists_sat_l,Formula.satisfies_conj_iff,
    rt_tuple_sat_l hKP.1,td_archive_source_sat_l (kp_pair_l hKP) hKP.1,Formula.satisfies_exists_iff,
    ic_common_sat_l hKP,Formula.satisfies_orderedPairMem_iff (kp_pair_l hKP),Formula.satisfies_disj_iff,
    Formula.satisfies_extensionalEq_iff_eq hKP.1,tg_root_square_sat_l hKP.1,
    td_archive_view_sat_l (kp_pair_l hKP),Definitional.Term.eval_weaken,
    Td_archive_row_d.from_values_d,rb_old_eval_l,Term.eval_bound,Fin.addCases_left,List.get]
  constructor
  · rintro ⟨v,tuple,source,rest⟩
    exact ⟨Td_archive_row_d.from_values_d v,by simpa only [Td_archive_row_d.values_from_l] using tuple,source,rest⟩
  · rintro ⟨s,tuple,source,rest⟩
    refine ⟨s.values_d,tuple,?_,?_⟩
    · change Td_archive_source_d (kp_pair_l hKP) _ _ _ _ _ _ (Td_archive_row_d.from_values_d s.values_d)
      rw [Td_archive_row_d.from_values_l]
      exact source
    · have ev := congrArg Td_archive_row_d.v (Td_archive_row_d.from_values_l s)
      have eX := congrArg Td_archive_row_d.X (Td_archive_row_d.from_values_l s)
      have eR := congrArg Td_archive_row_d.R (Td_archive_row_d.from_values_l s)
      have eL := congrArg Td_archive_row_d.L (Td_archive_row_d.from_values_l s)
      have eU := congrArg Td_archive_row_d.U (Td_archive_row_d.from_values_l s)
      have ep := congrArg Td_archive_row_d.p (Td_archive_row_d.from_values_l s)
      dsimp only [Td_archive_row_d.from_values_d] at ev eX eR eL eU ep
      simpa only [ev,eX,eR,eL,eU,ep,Definitional.Term.eval_newest] using rest

-- Ω,c₀,X₀,Ar,Sr,D,N,R,χ,c,e,a,z,h,D₀,q。
def td_archive_m {d} (g : Fin 16 → Term d) : Formula 1 d :=
  let r : Fin 16 → Term (2+d) := fun i => (g i).rename (Fin.natAdd 2)
  rb_forall_m (.imp (Formula.orderedPairMem kpair_convention_l (.bound ((0 : Fin 2).castAdd d))
    (.bound ((1 : Fin 2).castAdd d)) (r 5))
    (td_archive_entry_m (fun i => [r 0,r 1,r 2,r 3,r 4,r 6,r 7,r 8,r 9,r 10,r 11,r 12,r 13,
      .bound ((0 : Fin 2).castAdd d),.bound ((1 : Fin 2).castAdd d),r 14,r 15].get i)))

@[simp] theorem td_archive_closed_l {d} (g : Fin 16 → Term d)
    (hg : ∀ i, (g i).freeSupport = []) : (td_archive_m g).FreeClosed := by
  simp -implicitDefEqProofs [td_archive_m,Definitional.Formula.FreeClosed,hg,Fin.forall_fin_succ]

theorem td_archive_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (g : Fin 16 → Term d) :
    Formula.satisfies ρ (td_archive_m g) ↔
      Td_archive_d (kp_pair_l hKP) ((g 0).eval ρ) ((g 1).eval ρ) ((g 2).eval ρ) ((g 3).eval ρ)
        ((g 4).eval ρ) ((g 5).eval ρ) ((g 6).eval ρ) ((g 7).eval ρ) ((g 8).eval ρ)
        ((g 9).eval ρ) ((g 10).eval ρ) ((g 11).eval ρ) ((g 12).eval ρ) ((g 13).eval ρ)
        ((g 14).eval ρ) ((g 15).eval ρ) := by
  simp only [td_archive_m,rb_forall_sat_l,Formula.satisfies_imp_iff,
    Formula.satisfies_orderedPairMem_iff (kp_pair_l hKP),td_archive_entry_sat_l hKP,
    rb_old_eval_l,Term.eval_bound,Fin.addCases_left,List.get]
  exact ⟨fun h m r => h (fun i => [m,r].get i),fun h v => h (v 0) (v 1)⟩

def td_archive_links_m {d} (o Q G E D : Term d) : Formula 1 d :=
  let e : Term d → Term (75+d) := fun t => t.rename (Fin.natAdd 75)
  let v : Fin 75 → Term (75+d) := fun i => .bound (i.castAdd d)
  rb_forall_m (.imp (rd_entry0_m (v 73) (v 74) (e D))
    (.imp (rt_tuple_m (fun i : Fin 73 => v (i.castAdd 2)) (v 74))
      (.conj (rd_entry0_m (v 62) (v 63) (e Q))
        (.conj (it_map_m (e G) (e o) (v 62) (v 66))
          (set[75+d] ⟪∃ p κ F, ⌜rd_entry0_m⌝ₚ(⌜v 62⌝ₛ,p,⌜e E⌝ₛ) ∧
            ⌜it_payload_m⌝ₚ(p,κ,⌜v 67⌝ₛ,F)⟫)))))

@[simp] theorem td_archive_links_closed_l {d} (o Q G E D : Term d)
    (ho : o.freeSupport = []) (hq : Q.freeSupport = []) (hg : G.freeSupport = [])
    (he : E.freeSupport = []) (hd : D.freeSupport = []) :
    (td_archive_links_m o Q G E D).FreeClosed := by
  simp -implicitDefEqProofs [td_archive_links_m,Definitional.Formula.FreeClosed,ho,hq,hg,he,hd]
  exact rt_tuple_closed_l _ _ (fun _ => rfl) rfl

set_option maxRecDepth 2048 in
theorem td_archive_links_sat_l (hE : Extensional M) {d} (ρ : Env M d) (o Q G E D : Term d) :
    Formula.satisfies ρ (td_archive_links_m o Q G E D) ↔
      Td_archive_links_d (o.eval ρ) (Q.eval ρ) (G.eval ρ) (E.eval ρ) (D.eval ρ) := by
  simp only [td_archive_links_m,rb_forall_sat_l,Formula.satisfies_imp_iff,rd_entry0_sat_l hE,
    rt_tuple_sat_l hE,Formula.satisfies_conj_iff,it_map_sat_l hE,Formula.satisfies_exists_iff,
    it_payload_sat_l hE,Definitional.Term.eval_weaken,rb_old_eval_l,Term.eval_bound,Fin.addCases_left]
  constructor
  · intro h m r s entry tuple
    let v : Fin 75 → M.Domain := Fin.addCases (m := 73) (n := 2) s.values_d (Fin.cases m (fun _ => r))
    exact h v entry tuple
  · intro h v entry tuple
    let s := Td_archive_row_d.from_values_d (fun i : Fin 73 => v (i.castAdd 2))
    have pack : Rt_tuple_d s.values_d (v 74) := by simpa only [s,Td_archive_row_d.values_from_l] using tuple
    exact h (v 73) (v 74) s entry pack

def td_clear_m {d} (D n T : Term d) : Formula 1 d :=
  let e : Term d → Term (75+d) := fun t => t.rename (Fin.natAdd 75)
  let v : Fin 75 → Term (75+d) := fun i => .bound (i.castAdd d)
  rb_forall_m (.imp (rd_entry0_m (v 73) (v 74) (e D))
    (.imp (rt_tuple_m (fun i : Fin 73 => v (i.castAdd 2)) (v 74))
      (.neg (rd_entry0_m (v 62) (e n) (e T)))))

@[simp] theorem td_clear_closed_l {d} (D n T : Term d)
    (hd : D.freeSupport = []) (hn : n.freeSupport = []) (ht : T.freeSupport = []) :
    (td_clear_m D n T).FreeClosed := by
  simp -implicitDefEqProofs [td_clear_m,Definitional.Formula.FreeClosed,hd,hn,ht]
  exact rt_tuple_closed_l _ _ (fun _ => rfl) rfl

set_option maxRecDepth 2048 in
theorem td_clear_sat_l (hE : Extensional M) {d} (ρ : Env M d) (D n T : Term d) :
    Formula.satisfies ρ (td_clear_m D n T) ↔ Td_clear_d (D.eval ρ) (n.eval ρ) (T.eval ρ) := by
  simp only [td_clear_m,rb_forall_sat_l,Formula.satisfies_imp_iff,rd_entry0_sat_l hE,
    rt_tuple_sat_l hE,Formula.satisfies_neg_iff,rb_old_eval_l,Term.eval_bound,Fin.addCases_left]
  constructor
  · intro h m r s entry tuple
    let v : Fin 75 → M.Domain := Fin.addCases (m := 73) (n := 2) s.values_d (fun i => [m,r].get i)
    exact h v entry tuple
  · intro h v entry tuple
    let s := Td_archive_row_d.from_values_d (fun i : Fin 73 => v (i.castAdd 2))
    have pack : Rt_tuple_d s.values_d (v 74) := by simpa only [s,Td_archive_row_d.values_from_l] using tuple
    exact h (v 73) (v 74) s entry pack

end YesMetaZFC.SetTheory.LargeCardinal
