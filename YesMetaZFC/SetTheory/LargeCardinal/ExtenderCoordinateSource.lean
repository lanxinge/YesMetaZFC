import YesMetaZFC.SetTheory.LargeCardinal.ExtenderNormalSource
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderRepresentative

/-! # 源内坐标代表与坐标原子

坐标函数 s↦s(i) 在任意实际源中构造。坐标重排严格拉回这些函数；
扩展器的坐标等号和序条件随后精确读成商中的等号与隶属。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal FilterZF
universe u
variable {M : Structure.{u}}

def Ep_coord_d (κ D i f : M.Domain) : Prop := Fn0_d D κ f ∧
  ∀ s x, Rd_entry_d s x f ↔ M.mem s D ∧ Rd_entry_d i x s

def ep_coord_m {d} (κ D i f : Term d) : Formula 1 d := .conj (fn0_m D κ f)
  (.forallE (.forallE (.iff (rd_entry_m (.bound 1) .newest f.weaken.weaken)
    (.conj (.mem (.bound 1) D.weaken.weaken) (rd_entry_m i.weaken.weaken .newest (.bound 1))))))
derive_free_closed ep_coord_m

theorem ep_coord_sat_l (hE : Extensional M) {d} (ρ : Env M d) (κ D i f : Term d) :
    Formula.satisfies ρ (ep_coord_m κ D i f) ↔ Ep_coord_d (κ.eval ρ) (D.eval ρ) (i.eval ρ) (f.eval ρ) := by
  simp only [ep_coord_m, Ep_coord_d, Formula.satisfies_conj_iff, fn0_sat_l hE,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, rd_entry_sat_l hE,
    Formula.satisfies_mem_iff, Definitional.Term.eval_weaken]; rfl

theorem Ep_source_d.coordinate_l (hZF : M.Models ZF) {ω κ K X R n D i : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (hn : M.mem n ω) (hD : Ep_space_d κ n D) (hi : M.mem i n) :
    ∃ f, M.mem f X ∧ Ep_coord_d κ D i f := by
  obtain ⟨c, code⟩ := source.code
  let φ : BinarySchema 1 := { body := rd_entry0_m (.bound 2) .newest (.bound 1) }
  let ρ : Env M 1 := ⟨fun _ => i, fun _ => i⟩
  have sat s x : φ.denote ρ s x ↔ Rd_entry_d i x s := rd_entry0_sat_l hZF.1 ..
  obtain ⟨f, hfX, hf, select⟩ := sc_uniform_source_l hZF source.omega source.transitive code source.theory
    φ (rd_entry0_delta_l ..) ρ
    (fun _ => source.transitive ω source.omega_mem i (source.omega.transitive hZF n hn i hi))
    (source.space_mem_l hZF hn hD) source.cardinal_mem (fun s hs => by
      obtain ⟨x, hx, hix⟩ := ((hD s).mp hs).2.1 i hi
      exact ⟨x, hx, (sat s x).mpr hix⟩)
  have entry s x (hsx : Rd_entry_d s x f) := (sat s x).mp (select s x hsx)
  refine ⟨f, hfX, hf,
    fun s x => ⟨fun h => ⟨(hf.bound_l h).1, entry s x h⟩, ?_⟩⟩
  rintro ⟨hs, hix⟩
  obtain ⟨y, _, hsy⟩ := hf.2.1 s hs
  exact (fn0_function_l (ZF.modelsKP hZF) ((hD s).mp hs)).1.2 i y x (entry s y hsy) hix ▸ hsy

theorem Ep_coord_d.pull_l {κ X m n D E r i j f g : M.Domain}
    (hκX : M.MemberSubset κ X) (hD : Ep_space_d κ m D) (hE : Ep_space_d κ n E)
    (hr : Fn0_d m n r) (hij : Rd_entry_d i j r) (hf : Ep_coord_d κ D i f) (hg : Ep_coord_d κ E j g) :
    Ep_pull_d κ X m n r f g := by
  refine ⟨⟨D, hD, hf.1.mono_target_l hκX⟩, ⟨E, hE, hg.1.mono_target_l hκX⟩, fun s t hs ht x => ?_⟩
  exact (hg.2 s x).trans ((and_congr Iff.rfl (ht.value_l hr hs hij).symm).trans
    ⟨fun h => (hf.2 t x).mpr ⟨(hD t).mpr ht.1, h.2⟩,
      fun h => ⟨(hE s).mpr hs, ((hf.2 t x).mp h).2⟩⟩)

theorem ep_coordinate_atoms_l (hZF : M.Models ZF) {ω κ K X R L F n D a U i j α β f g : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (family : Em_source_d ω κ L X F)
    (atoms : Ea_atoms_d ω κ L F) (hn : M.mem n ω) (ha : Fn0_d n L a) (hD : Ep_space_d κ n D)
    (haU : Rd_entry_d a U F) (hi : Rd_entry_d i α a) (hj : Rd_entry_d j β a)
    (hf : Ep_coord_d κ D i f) (hg : Ep_coord_d κ D j g) :
    (Rp_eq_d X U f g ↔ α = β) ∧ (Rp_rel_d (kp_pair_l (ZF.modelsKP hZF)) X U R f g ↔ M.mem α β) := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨c, code⟩ := source.code
  have ultra := family.at_l hZF.1 haU ha hD
  have part (b : Bool) : (∃ A, M.mem A U ∧ ∀ s, M.mem s A → Rp_atom_d I b X R f g s) ↔
      if b then α = β else M.mem α β := by
    let ρ : Env M 3 := ⟨Fin.cases κ (Fin.cases i (fun _ => j)), fun _ => κ⟩
    let φ : UnarySchema 3 := { body := ea_test_m b (.bound 1) (.bound 2) (.bound 3) .newest }
    have hnat t (ht : M.mem t n) := source.transitive ω source.omega_mem t (source.omega.transitive hZF n hn t ht)
    obtain ⟨B, hBX, bs⟩ := sc_separate_source_l I hZF source.omega source.transitive code source.theory
      φ (ea_test_delta_l ..) ρ (Fin.cases source.cardinal_mem (Fin.cases (hnat i (ha.bound_l hi).1)
        (fun _ => hnat j (ha.bound_l hj).1))) (source.space_mem_l hZF hn hD)
    have read s : M.mem s B ↔ M.mem s D ∧ Ea_test_d b κ i j s :=
      (bs s).trans (and_congr_right fun _ => ea_test_sat_l hZF.1 ..)
    obtain ⟨B', bs', value⟩ := atoms b n a U i j α β hn ha haU hi hj
    have eB := hZF.1.eq_of_same_members B' B fun s => (bs' s).trans ((and_congr (hD s).symm Iff.rfl).trans (read s).symm)
    subst B'
    have point s (hs : M.mem s D) : Rp_atom_d I b X R f g s ↔ Ea_test_d b κ i j s := by
      obtain ⟨x, hx, hsx⟩ := hf.1.2.1 s hs
      obtain ⟨y, hy, hsy⟩ := hg.1.2.1 s hs
      have hix := ((hf.2 s x).mp hsx).2
      have hjy := ((hg.2 s y).mp hsy).2
      rw [ea_test_read_l b ((hD s).mp hs) hix hjy]
      have hxX := source.transitive κ source.cardinal_mem x hx
      have hyX := source.transitive κ source.cardinal_mem y hy
      constructor
      · rintro ⟨x', _, y', _, hsx', hsy', h⟩
        have ex := (fn0_function_l (ZF.modelsKP hZF) hf.1).1.2 s x' x hsx' hsx
        have ey := (fn0_function_l (ZF.modelsKP hZF) hg.1).1.2 s y' y hsy' hsy
        subst x' y'
        cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
        · exact ((code.2 x y).mp h).2.2
        · exact h
      · intro h
        refine ⟨x, hxX, y, hyX, hsx, hsy, ?_⟩
        cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
        · exact (code.2 x y).mpr ⟨hxX, hyX, h⟩
        · exact h
    apply Iff.trans ?_ value
    exact ⟨fun ⟨A, hAU, hA⟩ => ultra.upward A B hAU hBX (fun s hs => ((read s).mp hs).1)
      (fun s hs => (read s).mpr ⟨ultra.base.bounds A hAU s hs, (point s (ultra.base.bounds A hAU s hs)).mp (hA s hs)⟩),
      fun hB => ⟨B, hB, fun s hs => (point s ((read s).mp hs).1).mpr ((read s).mp hs).2⟩⟩
  exact ⟨(rp_atom_eq_l I (R := R)).symm.trans (part true), part false⟩

end YesMetaZFC.SetTheory.LargeCardinal
