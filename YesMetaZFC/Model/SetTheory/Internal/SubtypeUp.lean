import YesMetaZFC.Model.SetTheory.Internal.SubtypeQuery

/-! # 子类型查询沿秩层扩大保持为真

完整满足关系并不向上绝对；这里只运输子类型句子的实际较低秩见证。
先读取句子自身的类型条件，再在高层复用同一见证，最后回到同一程序。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "Q" => kp_pair_l (ZF.modelsKP hZF)
local notation "K" => fp_interpretation_l (ZF.models_kpi_l hZF)

theorem ts_template_up_l {ω ν μ X Y : M.Domain} (hω : M.IsOmega ω)
    (hX : V_d Q ν X) (hY : V_d Q μ Y) (sub : M.MemberSubset ν μ) (hwX : M.mem ω X)
    (ρ : Env (rt_model_l X ⟨⟨ω, hwX⟩⟩) 8) (hw : (ρ.bound 7).val = ω) :
    Formula.satisfies ρ ts_template_m →
      Formula.satisfies (image_env_l (N := rt_model_l Y ⟨⟨ω, ZF.v_mono_l Q hZF hX hY sub ω hwX⟩⟩)
        (fun x : {x // M.mem x X} =>
        (⟨x.val, ZF.v_mono_l Q hZF hX hY sub x.val x.property⟩ : {x // M.mem x Y})) ρ) ts_template_m := by
  let e : {x // M.mem x X} → {x // M.mem x Y} :=
    fun x => ⟨x.val, ZF.v_mono_l Q hZF hX hY sub x.val x.property⟩
  let ε := image_env_l (N := rt_model_l Y ⟨⟨ω, ZF.v_mono_l Q hZF hX hY sub ω hwX⟩⟩) e ρ
  have hwY := ZF.v_mono_l Q hZF hX hY sub ω hwX
  intro truth
  obtain ⟨hκ, hτ, hτκ, hm⟩ := ts_below_guard_l (ZF.v_transitive_l Q hZF hX) _ (ZF.modelsKP hZF)
    ρ (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest truth
  change M.mem (ρ.bound 3).val (ρ.bound 7).val at hm
  rw [hw] at hm
  obtain ⟨C, hc⟩ := ZF.v_exists_l Q hZF hκ.1
  obtain ⟨B, U, hb, _, constants⟩ := tt_constants_exists_l hZF hc hκ hτκ
  obtain ⟨D, pool⟩ := tt_pool_exists_l Q hZF hω (ρ.bound 3).val U
  have down := ts_below_source_l hZF hω hX hwX ρ (.bound 7) (.bound 6) (.bound 5) (.bound 4)
    (.bound 3) (.bound 2) (.bound 1) .newest (Subtype.ext hw) hκ hτ hτκ hm hb constants pool
  have up := ts_below_source_l hZF hω hY hwY ε (.bound 7) (.bound 6) (.bound 5) (.bound 4)
    (.bound 3) (.bound 2) (.bound 1) .newest (Subtype.ext hw) hκ hτ hτκ hm hb constants pool
  have ⟨nm, below⟩ := down.mp truth
  exact up.mpr ⟨nm, below.mono_l hZF sub⟩

theorem Ts_program_d.up_l {ω n b a z ν μ X Y c R d S f : M.Domain} (hω : M.IsOmega ω)
    {σ : Fin 7 → M.Domain} (prog : Ts_program_d hZF ω n b σ a z)
    (hX : V_d Q ν X) (hY : V_d Q μ Y) (sub : M.MemberSubset ν μ)
    (lower : Smem_d Q c X R) (upper : Smem_d Q d Y S)
    (ff : M.IsSetFunctionFromTo Q f ω X) (fw : Rd_entry_d (σ 6) ω f) :
    Satisfies_d Q ω c a f → Satisfies_d Q ω d a f := by
  have below := ZF.v_mono_l Q hZF hX hY sub
  have hwX := ff.output_mem_of_pairMember fw
  have slot i := ff.2.2 (σ i) (hω.transitive hZF b prog.length (σ i) (prog.slots i))
  obtain ⟨x₀, hx₀, fx₀⟩ := slot 0
  obtain ⟨x₁, hx₁, fx₁⟩ := slot 1
  obtain ⟨x₂, hx₂, fx₂⟩ := slot 2
  obtain ⟨x₃, hx₃, fx₃⟩ := slot 3
  obtain ⟨x₄, hx₄, fx₄⟩ := slot 4
  obtain ⟨x₅, hx₅, fx₅⟩ := slot 5
  let ρ : Env (smdl_structure_l Q (R := R) lower.1.2.1) 7 :=
    ⟨Fin.cases ⟨x₀, hx₀⟩ (Fin.cases ⟨x₁, hx₁⟩ (Fin.cases ⟨x₂, hx₂⟩ (Fin.cases ⟨x₃, hx₃⟩
      (Fin.cases ⟨x₄, hx₄⟩ (Fin.cases ⟨x₅, hx₅⟩ (fun _ => ⟨ω, hwX⟩)))))), fun _ => ⟨ω, hwX⟩⟩
  have vals : ∀ i, Rd_entry_d (σ i) (ρ.bound i).val f :=
    Fin.cases fx₀ (Fin.cases fx₁ (Fin.cases fx₂ (Fin.cases fx₃ (Fin.cases fx₄ (Fin.cases fx₅
      (Fin.cases fw (fun i => Fin.elim0 i)))))))
  let e : {x // M.mem x X} → {x // M.mem x Y} := fun x => ⟨x.val, below x.val x.property⟩
  let ρ' := image_env_l (N := smdl_structure_l Q (R := S) upper.1.2.1) e ρ
  obtain ⟨g, fg, agree⟩ := fn_recode_l Q K hZF ff
  have ffY : M.IsSetFunctionFromTo Q f ω Y := ⟨ff.1, ff.2.1,
    fun i hi => (ff.2.2 i hi).imp fun x hx => ⟨below x hx.1, hx.2⟩⟩
  have fgY : M.IsSetFunctionFromTo K g ω Y := ⟨fg.1, fg.2.1,
    fun i hi => (fg.2.2 i hi).imp fun x hx => ⟨below x hx.1, hx.2⟩⟩
  intro truth
  obtain ⟨p, code, atom⟩ := (prog.compile ν X c R f g lower ρ hX hwX ff fg agree fw vals).mp truth
  apply (prog.compile μ Y d S f g upper ρ' hY (below ω hwX) ffY fgY agree fw vals).mpr
  refine ⟨e p, code.mono_l K below, ?_⟩
  let ε : Env (rt_model_l X ⟨⟨ω, hwX⟩⟩) 8 := ⟨(ρ.push p).bound, (ρ.push p).free⟩
  have step := ts_template_up_l hZF hω hX hY sub hwX ε rfl
    ((smem_formula_l Q lower _ ts_template_m ε).mpr atom)
  have lift := (smem_formula_l Q upper ⟨⟨ω, below ω hwX⟩⟩ ts_template_m
    (image_env_l (N := rt_model_l Y ⟨⟨ω, below ω hwX⟩⟩) e ε)).mp step
  change Formula.satisfies (image_env_l (N := smdl_structure_l Q (R := S) upper.1.2.1) e (ρ.push p)) ts_template_m at lift
  have eq := @image_env_push_l (smdl_structure_l Q (R := R) lower.1.2.1)
    (smdl_structure_l Q (R := S) upper.1.2.1) e 7 ρ p
  exact (congrArg (fun ε => Formula.satisfies ε ts_template_m) eq).mp lift

end YesMetaZFC.SetTheory.Internal
