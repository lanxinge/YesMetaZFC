import YesMetaZFC.SetTheory.Collapse.RelationSyntax
import YesMetaZFC.Model.SetTheory.DependentChoice
import YesMetaZFC.SetTheory.InnerModel.Recursion.Composition

/-! # 内部良基性、下降序列与关系保持映射

良基性排除内部 ω 下降序列只用 ZF；反向使用原 DC 句子的实际解释。
所有序列均为模型内部的函数图，因而不要求模型外良基或 ω 标准。
-/
namespace YesMetaZFC.SetTheory
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Wf_desc_d (R f : M.Domain) : Prop := ∀ i j x y, M.SuccessorOf j i →
  Rd_entry_d i x f → Rd_entry_d j y f → Rd_entry_d y x R

/-- 对一条实际下降图作内部归纳，保持由既有关系图编码的不变量。 -/
theorem wf_desc_invariant_l (hZF : M.Models ZF) {ω C R f W H z x₀ : M.Domain} (hω : M.IsOmega ω)
    (fn : Fn0_d ω C f) (desc : Wf_desc_d R f) (hz : ∀ x, ¬ M.mem x z)
    (h₀ : Rd_entry_d z x₀ f) (initial : Rd_entry_d x₀ H W)
    (closed : ∀ x y, M.mem x C → M.mem y C → Rd_entry_d x y R → Rd_entry_d y H W → Rd_entry_d x H W) :
    ∀ i x, Rd_entry_d i x f → Rd_entry_d x H W := by
  let ρ : Env M 3 := ⟨Fin.cases f (Fin.cases H (fun _ => W)), fun _ => f⟩
  let φ : UnarySchema 3 := { body := .forallE (.imp (rd_entry0_m (.bound 1) .newest (.bound 2))
    (rd_entry0_m .newest (.bound 3) (.bound 4))) }
  have sat i : φ.denote ρ i ↔ ∀ x, Rd_entry_d i x f → Rd_entry_d x H W := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, rd_entry0_sat_l hZF.1]; rfl
  have all : ∀ i, M.mem i ω → φ.denote ρ i := by
    apply hω.induction (fun i => φ.denote ρ i) (ZF.separation_exists_d hZF φ ρ ω)
    · intro z' hz'
      have eq := hZF.1.eq_of_same_members z' z (fun x => iff_of_false (hz' x) (hz x))
      subst z'
      exact (sat z).mpr (fun x hx => (fn0_function_l (ZF.modelsKP hZF) fn).1.2 z x x₀ hx h₀ |>.symm ▸ initial)
    · intro i hi ih k hik
      apply (sat k).mpr
      intro x hkx
      obtain ⟨y, hy, hiy⟩ := fn.2.1 i hi
      exact closed x y (fn.bound_l hkx).2 hy (desc i k y x hik hiy hkx) ((sat i).mp ih y hiy)
  exact fun i x hix => (sat i).mp (all i (fn.bound_l hix).1) x hix

theorem wf_no_desc_l (hZF : M.Models ZF) {ω X R f : M.Domain} (hω : M.IsOmega ω)
    (hw : Wf_rel_d X R) (hf : Fn0_d ω X f) : ¬ Wf_desc_d R f := by
  intro hd
  let I := kp_pair_l (ZF.modelsKP hZF)
  have fn := fn0_function_l (ZF.modelsKP hZF) hf
  obtain ⟨Y, hY⟩ := ZF.exists_range_of_setFunction hZF I fn.1 fn.2.1
  obtain ⟨z, _, hzω⟩ := hω.1.1
  obtain ⟨x, _, hzx⟩ := hf.2.1 z hzω
  obtain ⟨a, ha, hm⟩ := hw Y (fun y hy => ((hY y).mp hy).elim fun _ hh => (hf.bound_l hh).2)
    ⟨x, (hY x).mpr ⟨z, hzx⟩⟩
  obtain ⟨i, hia⟩ := (hY a).mp ha
  obtain ⟨j, hij, hjω⟩ := hω.1.2 i (hf.bound_l hia).1
  obtain ⟨b, _, hjb⟩ := hf.2.1 j hjω
  exact hm b ((hY b).mpr ⟨j, hjb⟩) (hd i j a b hij hia hjb)

theorem wf_of_no_desc_l (hZF : M.Models ZF) {ω X R : M.Domain}
    (hDC : Dc_d (kp_pair_l (ZF.modelsKP hZF)) ω)
    (hn : ∀ f, Fn0_d ω X f → ¬ Wf_desc_d R f) : Wf_rel_d X R := by
  classical
  intro Y hY hne
  apply Classical.byContradiction
  intro hmin
  let I := kp_pair_l (ZF.modelsKP hZF)
  let φ : BinarySchema 1 := { body := rd_entry_m .newest (.bound 1) (.bound 2) }
  obtain ⟨S, _, hs⟩ := ZF.exists_setRelationOn_of_denote hZF I φ ⟨fun _ => R, fun _ => R⟩ Y
  have spec x y : Rd_entry_d x y S ↔ M.mem x Y ∧ M.mem y Y ∧ Rd_entry_d y x R :=
    (hs x y).trans (and_congr_right fun _ => and_congr_right fun _ => rd_entry_sat_l hZF.1 _ _ _ _)
  obtain ⟨a, ha⟩ := hne
  obtain ⟨f, hf, _, hd⟩ := hDC Y S a ha (fun x hx => by
    have : ∃ y, M.mem y Y ∧ Rd_entry_d y x R := by
      apply Classical.byContradiction
      intro hh
      exact hmin ⟨x, hx, fun y hy hyx => hh ⟨y, hy, hyx⟩⟩
    exact this.imp fun y hy => ⟨hy.1, (spec x y).mpr ⟨hx, hy⟩⟩)
  exact hn f ((fn0_of_function_l (ZF.modelsKP hZF) hf).mono_target_l hY)
    (fun i j x y hij hx hy => ((spec x y).mp (hd i j x y hij hx hy)).2.2)

/-- 沿实际关系保持映射回拉良基性；无需单射，也无需选择。 -/
theorem wf_of_map_l (hZF : M.Models ZF) {X R Y S f : M.Domain} (hw : Wf_rel_d Y S)
    (hf : Fn0_d X Y f)
    (he : ∀ a b x y, Rd_entry_d a b R → Rd_entry_d a x f → Rd_entry_d b y f → Rd_entry_d x y S) :
    Wf_rel_d X R := by
  intro B hB hne
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨g, hg⟩ := ZF.exists_restriction hZF I f B
  have fn := hg.isSetFunctionFromTo (fn0_function_l (ZF.modelsKP hZF) hf) hB
  obtain ⟨C, hC⟩ := ZF.exists_range_of_setFunction hZF I fn.1 fn.2.1
  obtain ⟨a, ha⟩ := hne
  obtain ⟨x, _, hax⟩ := fn.2.2 a ha
  obtain ⟨x, hx, hm⟩ := hw C (fun y hy => ((hC y).mp hy).elim fun _ hh => fn.output_mem_of_pairMember hh)
    ⟨x, (hC x).mpr ⟨a, hax⟩⟩
  obtain ⟨a, hax⟩ := (hC x).mp hx
  refine ⟨a, fn.input_mem_of_pairMember hax, fun b hb hba => ?_⟩
  obtain ⟨y, _, hby⟩ := fn.2.2 b hb
  exact hm y ((hC y).mpr ⟨b, hby⟩) (he b a y x hba ((hg.2 b y).mp hby).2 ((hg.2 a x).mp hax).2)

/-- 满射商的关系由任意代表读取时，商与代表关系具有相同的内部良基性。 -/
theorem wf_quotient_l (hZF : M.Models ZF) {A P C S q : M.Domain} (hq : Fn0_d A C q)
    (hr : ∀ B, M.mem B C → ∃ x, Rd_entry_d x B q)
    (he : ∀ x y B D, Rd_entry_d x B q → Rd_entry_d y D q → (Rd_entry_d B D S ↔ Rd_entry_d x y P)) :
    Wf_rel_d C S ↔ Wf_rel_d A P := by
  refine ⟨fun hw => wf_of_map_l hZF hw hq (fun x y B D hxy hx hy => (he x y B D hx hy).mpr hxy),
    fun hw Y hY hne => ?_⟩
  let φ : UnarySchema 2 := { body := Formula.existsMem (.bound 1) (rd_entry_m (.bound 1) .newest (.bound 3)) }
  let ρ : Env M 2 := (⟨fun _ => q, fun _ => q⟩ : Env M 1).push Y
  obtain ⟨B, hb⟩ := ZF.separation_exists_d hZF φ ρ A
  have spec x : M.mem x B ↔ M.mem x A ∧ ∃ D, M.mem D Y ∧ Rd_entry_d x D q := by
    simpa only [φ, Formula.satisfies_existsMem_iff, rd_entry_sat_l hZF.1] using! hb x
  obtain ⟨D, hD⟩ := hne
  obtain ⟨x, hx⟩ := hr D (hY D hD)
  obtain ⟨a, ha, hm⟩ := hw B (fun x hx => ((spec x).mp hx).1)
    ⟨x, (spec x).mpr ⟨(hq.bound_l hx).1, D, hD, hx⟩⟩
  obtain ⟨_, D, hDY, haD⟩ := (spec a).mp ha
  refine ⟨D, hDY, fun E hE hED => ?_⟩
  obtain ⟨b, hbE⟩ := hr E (hY E hE)
  exact hm b ((spec b).mpr ⟨(hq.bound_l hbE).1, E, hE, hbE⟩) ((he b a E D hbE haD).mp hED)

end YesMetaZFC.SetTheory
