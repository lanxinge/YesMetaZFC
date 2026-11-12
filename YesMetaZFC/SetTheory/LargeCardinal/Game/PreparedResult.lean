import YesMetaZFC.SetTheory.LargeCardinal.Game.SavedNode
import YesMetaZFC.SetTheory.LargeCardinal.Game.Subtype
import YesMetaZFC.Model.SetTheory.Relations.RecordImage
import YesMetaZFC.SetTheory.LargeCardinal.Types.RawSubtype
import YesMetaZFC.Model.SetTheory.Relations.SliceEmbedding
import YesMetaZFC.SetTheory.LargeCardinal.Types.ContinueAbsolute
import YesMetaZFC.SetTheory.LargeCardinal.Types.ContinueScope
import YesMetaZFC.SetTheory.LargeCardinal.Game.ContinueNative
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawRankSource
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyOriginalResult

/-! # 同一原边上的完整存档与 subtype 返回目标反射层

完整五十六项记录沿实际初等图搬运，再以原图的单值性核对五个关键坐标。
查询自身和原自然数程序使其余参数回到反射层；完整名字域由该模型自己的
极限秩层构造，因而原 subtype 保持同一个查询和类型。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_saved_d.subtype_image_l {Ω w Y S η C L V r c d Z T j : M.Domain}
    (old : Tg_saved_d I w Y S η C L V r) {v : Fin 54 → M.Domain}
    (code : Tg_saved_code_d Y S w V r v) (hΩ : M.IsOmega Ω)
    (mx : Smdl_d I c Y S) (my : Smdl_d I d Z T) (map : Smap_d I Ω c d Y Z j)
    (ground : (smdl_structure_l I (R := T) my.2.1).Models ZF)
    (ρ : Env (smdl_structure_l I (R := T) my.2.1) 17)
    (omega : (smdl_structure_l I (R := T) my.2.1).IsOmega (ρ.bound 0))
    (arity : (smdl_structure_l I (R := T) my.2.1).mem (ρ.bound 1) (ρ.bound 0))
    (program : ∀ i : Fin 9, (smdl_structure_l I (R := T) my.2.1).mem
      (ρ.bound ([7,8,10,11,12,13,14,15,16].get i)) (ρ.bound 0))
    (points : ∀ i : Fin 5, Rd_entry_d (v ([16,24,15,13,11].get i))
      (ρ.bound ([0,1,2,5,9].get i)).val j)
    (valid : Formula.satisfies ρ tg_subtype0_m) :
    ∃ η' C' L' V' r', Rd_entry_d w (ρ.bound 0).val j ∧ Rd_entry_d η η' j ∧ Rd_entry_d C C' j ∧
      Rd_entry_d L L' j ∧ Rd_entry_d V V' j ∧ Rd_entry_d r r' j ∧
    ∃ saved : Tg_saved_d I (ρ.bound 0).val Z T η' C' L' V' r',
    ∃ nc : Nonempty {x : (smdl_structure_l I (R := T) my.2.1).Domain //
      (smdl_structure_l I (R := T) my.2.1).mem x ⟨C', saved.context.member⟩},
    ∃ ψ : Env (rt_model_l (M := smdl_structure_l I (R := T) my.2.1) ⟨C', saved.context.member⟩ nc) 54,
    ∃ θ : Env (rt_model_l (M := smdl_structure_l I (R := T) my.2.1) ⟨C', saved.context.member⟩ nc) 17,
      Tg_saved_code_d Z T (ρ.bound 0).val V' r' (fun i => (ψ.bound i).val.val) ∧
      Formula.satisfies ψ tg_round0_m ∧ (∀ i, Rd_entry_d (v i) (ψ.bound i).val.val j) ∧
      (∀ i, (θ.bound i).val = ρ.bound i) ∧ Formula.satisfies θ tg_subtype0_m ∧
      ∀ i : Fin 5, θ.bound ([0,1,2,5,9].get i) = ψ.bound ([16,24,15,13,11].get i) := by
  let N := smdl_structure_l I (R := T) my.2.1
  have hN := ZF.modelsKP ground
  obtain ⟨_, χ₀, code₀, _, hw₀, _⟩ := old.read_l I hZF.1
  have same := code.inj_l I hZF.1 code₀
  have hw : v 16 = w := (show v 16 = (χ₀.bound 16).val.val from congrFun same 18).trans hw₀
  have iw : Rd_entry_d w (ρ.bound 0).val j := hw ▸ points 0
  obtain ⟨η', C', iη, iC, current⟩ := old.context.map_l hZF hΩ mx my map iw
  let D : N.Domain := ⟨C', current.member⟩
  have fs : Fs_read_d (ρ.bound 0) D := current.finite_l my.2.1 ground.1
  let nc : Nonempty {x : N.Domain // N.mem x D} := ⟨⟨ρ.bound 0, fs.omega_mem⟩⟩
  obtain ⟨r', χ, ir, images, record, tuple, truth⟩ :=
    map.record_image_l I hZF hΩ mx my ground.1 D iC fs.transitive nc
      tg_saved_record0_m tg_saved_record0_closed_l old.record ((tg_saved_code_read_l I hZF.1).mp code).2
  let ψ : Env (rt_model_l D nc) 54 := χ.reindex (fun i => i.succ.succ)
  have round : Formula.satisfies ψ tg_round0_m :=
    (Formula.satisfies_rename ..).mp ((Formula.satisfies_conj_iff ..).mp truth).1
  have image i : Rd_entry_d (v i) (ψ.bound i).val.val j := images i.succ.succ
  have links (i : Fin 5) : ρ.bound ([0,1,2,5,9].get i) = (ψ.bound ([16,24,15,13,11].get i)).val :=
    Subtype.ext (map.1.1.1.2 _ _ _ (points i) (image _))
  have ew : (χ.bound 0).val = ρ.bound 0 := Subtype.ext (map.1.1.1.2 _ _ _ (images 0) iw)
  let V' := (χ.bound 1).val.val
  obtain ⟨L', _, iL⟩ := map.1.1.2.2 L (old.limit.elim fun mem _ => mem 0)
  have limit := old.limit.map_l I hZF hΩ mx my map (by simp -implicitDefEqProofs) (fun _ => iL)
  have rank : Rr_truth_d I Z T (v_sigma_m (.bound 1) .newest) (Fin.cases V' (fun _ => L')) :=
    old.rank.map_l I hZF hΩ mx my map (by simp -implicitDefEqProofs)
    (Fin.cases (images 1) (fun _ => iL))
  have member := (map.relation_l I hZF hΩ mx my (images 1) iC).mp old.member
  have ext := map.extensional_l hZF hΩ mx my old.ext
  obtain ⟨a, ha, b, hb, _⟩ := (rf_tuple_native_l I my.2.1 ground.1 (fun i => (χ.bound i).val) r').mp tuple
  have head : ∃ s, Rf_tuple_d I Z T (Fin.cases (ρ.bound 0).val (Fin.cases V' (fun _ : Fin 1 => s))) r'.val := by
    let v' : Fin 3 → N.Domain := Fin.cases (χ.bound 0).val (Fin.cases (χ.bound 1).val (fun _ => b))
    have out := (rf_tuple_native_l I my.2.1 ground.1 v' r').mpr ⟨a, ha, b, hb, rfl⟩
    have eq : (fun i => (v' i).val) =
        (Fin.cases (ρ.bound 0).val (Fin.cases V' (fun _ : Fin 1 => b.val))) :=
      funext (Fin.cases (congrArg Subtype.val ew) (Fin.cases rfl (fun _ => rfl)))
    exact ⟨b.val, eq ▸ out⟩
  let saved : Tg_saved_d I (ρ.bound 0).val Z T η' C' L' V' r'.val :=
    ⟨ext, current, limit, member, rank, record, head⟩
  have row : (fun i : Fin 56 => (χ.bound i).val.val) =
      Fin.cases (ρ.bound 0).val (Fin.cases V' (fun i => (ψ.bound i).val.val)) :=
    funext (Fin.cases (congrArg Subtype.val ew) (Fin.cases rfl (fun _ => rfl)))
  have code' := (tg_saved_code_read_l I hZF.1).mpr ⟨ext, row ▸ tuple⟩
  let slots : Fin 7 → Term 17 := Fin.cases (.bound 10) (Fin.cases (.bound 11) (Fin.cases (.bound 12)
    (Fin.cases (.bound 13) (Fin.cases (.bound 14) (Fin.cases (.bound 15) (fun _ => .bound 16))))))
  have subtype := (ts_subtype_sat_l hN ρ (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4)
    (.bound 5) (.bound 6) (.bound 7) (.bound 8) (.bound 9) slots).mp valid
  have facts := subtype
  obtain ⟨_, _, _, query, _⟩ := facts
  obtain ⟨hv, hm, hn, hτ, hκ, hω⟩ := query.constants
  have hU : N.mem (ρ.bound 5) D := by rw [show ρ.bound 5 = (ψ.bound 13).val from links 3]; exact (ψ.bound 13).property
  have hu : N.mem (ρ.bound 9) D := by rw [show ρ.bound 9 = (ψ.bound 11).val from links 4]; exact (ψ.bound 11).property
  have low i (hi : N.mem (ρ.bound i) (ρ.bound 5)) := fs.transitive _ hU _ hi
  have prog i := fs.transitive _ fs.omega_mem _ (program i)
  have members : ∀ i, N.mem (ρ.bound i) D := by
    simp only [Fin.forall_fin_succ]
    exact ⟨low 0 hω, low 1 hn, low 2 hκ, low 3 hτ, low 4 hm, hU, low 6 hv,
      prog 0, prog 1, hu, prog 2, prog 3, prog 4, prog 5, prog 6, prog 7, prog 8, fun i => Fin.elim0 i⟩
  let θ : Env (rt_model_l D nc) 17 := ⟨fun i => ⟨ρ.bound i, members i⟩, fun _ => ⟨ρ.bound 0, members 0⟩⟩
  let η₀ : N.Domain := ⟨η', current.height⟩
  have rankC : V_d (kp_pair_l hN) η₀ D := (rr_rank_native_l I my.2.1 hN η₀ D).mp
    ((rr_rank_truth_l I).mpr current.rank)
  have limitC : N.IsLimitOrdinal η₀ := (Formula.satisfies_isLimitOrdinal_iff ..).mp
    ((rr_truth_native_l I my.2.1 (Formula.isLimitOrdinal .newest) (by simp -implicitDefEqProofs)
      (fun _ : Fin 1 => η₀)).mp current.limit)
  obtain ⟨A, names⟩ := tn_names_exists_l ground (ρ.bound 1) (ρ.bound 5)
  have hA := names.rank_mem_l (ZF.modelsKP ground) omega rankC limitC fs.omega_mem arity hU
  have values : (fun i => ((slots i).eval θ).val) = (fun i => (slots i).eval ρ) := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))))) i
  have reflected : Formula.satisfies θ tg_subtype0_m :=
    ts_subtype_reflect_l hN fs.transitive nc θ (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4)
      (.bound 5) (.bound 6) (.bound 7) (.bound 8) (.bound 9) slots hA names (values.symm ▸ subtype)
  exact ⟨η', C', L', V', r'.val, iw, iη, iC, iL, images 1, ir, saved, nc, ψ, θ, code', round, image,
    fun _ => rfl, reflected, fun i => Subtype.ext (links i)⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 同一完整代表池把子类型送入实际原后继

旧常量域、类型及名字域属于原切片 β 时，其超幂像自动属于同一个有界池。
其余查询参数由子类型本身和原自然数程序回收。整条查询经该池的完整同构
传入实际原后继。原存档沿同一边完整搬运，五个关键坐标由原图单值性核对，
subtype 再返回这份存档所在的反射层；完整数值程序经同一共同根进入该层。
原系统与完整工厂证书同时保留。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Er_subtype_d (ω c X R c' Y S q Γ k N S₀ z c₁ : M.Domain)
    (nx : ∃ x, M.mem x N) (hN : (smdl_structure_l I (R := S₀) nx).Models KP)
    (U₀ w ξ ℓ e β X' K' jN U u : (smdl_structure_l I (R := S₀) nx).Domain)
    (ρ : Env (smdl_structure_l I (R := S₀) nx) 17)
    (wₚ ηₚ Cₚ Lₚ Vₚ rₚ : M.Domain) (v₀ : Fin 54 → M.Domain) : Prop :=
  ρ.bound 0 = w ∧ (smdl_structure_l I (R := S₀) nx).mem (ρ.bound 1) w ∧
  (smdl_structure_l I (R := S₀) nx).mem w β ∧ (smdl_structure_l I (R := S₀) nx).mem ξ β ∧
  (smdl_structure_l I (R := S₀) nx).mem U β ∧ (smdl_structure_l I (R := S₀) nx).mem u β ∧
  Rd_entry_d (M := smdl_structure_l I (R := S₀) nx) w w jN ∧
  Rd_entry_d (M := smdl_structure_l I (R := S₀) nx) (ρ.bound 1) (ρ.bound 1) jN ∧
  Rd_entry_d (M := smdl_structure_l I (R := S₀) nx) ξ (ρ.bound 2) jN ∧
  Rd_entry_d (M := smdl_structure_l I (R := S₀) nx) U (ρ.bound 5) jN ∧
  Rd_entry_d (M := smdl_structure_l I (R := S₀) nx) u (ρ.bound 9) jN ∧
  (∀ j : Fin 9, (smdl_structure_l I (R := S₀) nx).mem
    (ρ.bound ([7,8,10,11,12,13,14,15,16].get j)) w) ∧
  Smdl_d I c' Y S ∧ Tg_saved_d I wₚ Y S ηₚ Cₚ Lₚ Vₚ rₚ ∧ Tg_saved_code_d Y S wₚ Vₚ rₚ v₀ ∧
  (∀ i : Fin 5, Rd_entry_d ([w,ρ.bound 1,ξ,U,u].get i).val (v₀ ([16,24,15,13,11].get i)) k) ∧
  ∃ L J O Z A p T V r o C W j q' p₀,
    Er_rank_cut_at_d hZF ω c X R c' Y S q Γ k N S₀ z c₁ nx hN U₀ w ξ ℓ e β X' K' jN
      L J O Z A p T V r o C W j q' p₀ ∧
    ∃ next : Smdl_d I o C W,
    ∃ A₁ Q₁ Y₁ e₁ : (smdl_structure_l I (R := S₀) nx).Domain, ∃ D₁ Γ₁ t,
      Eb_collapse_d w ξ ℓ K' X' β e A₁ Q₁ Y₁ e₁ ∧
      (∀ x, M.mem x D₁ ↔ M.mem x N ∧ Rd_entry_d x A₁.val S₀) ∧
      (∀ x, M.mem x Γ₁ ↔ M.mem x N ∧ Rd_entry_d x Y₁.val S₀) ∧
      M.IsSetInjectionFromTo I t Γ₁ C ∧ Er_present_d I ω L N S₀ z Γ Y k r e₁.val D₁ t ∧
      (∀ x E, Rd_entry_d x E t → ∀ P,
        Rd_entry_d P E W ↔ ∃ y, Rd_entry_d y x S₀ ∧ Rd_entry_d y P t) ∧
      (∀ x y : (smdl_structure_l I (R := S₀) nx).Domain, ∀ b E,
        (smdl_structure_l I (R := S₀) nx).mem x β → Rd_entry_d x y jN →
        Rd_entry_d x.val b k → (Rd_entry_d y.val E t ↔ Rd_entry_d b E j)) ∧
      ∃ η : Env (smdl_structure_l I (R := W) next.2.1) 17,
        (∀ i, Rd_entry_d (ρ.bound i).val (η.bound i).val t) ∧ Formula.satisfies η tg_subtype0_m ∧
      ∃ η₁ C₁ L₁ V₁ r₁, Rd_entry_d wₚ (η.bound 0).val j ∧ Rd_entry_d ηₚ η₁ j ∧ Rd_entry_d Cₚ C₁ j ∧
        Rd_entry_d Lₚ L₁ j ∧ Rd_entry_d Vₚ V₁ j ∧ Rd_entry_d rₚ r₁ j ∧
      ∃ saved : Tg_saved_d I (η.bound 0).val C W η₁ C₁ L₁ V₁ r₁,
      ∃ nc : Nonempty {x : (smdl_structure_l I (R := W) next.2.1).Domain //
        (smdl_structure_l I (R := W) next.2.1).mem x ⟨C₁, saved.context.member⟩},
      ∃ ψ : Env (rt_model_l (M := smdl_structure_l I (R := W) next.2.1) ⟨C₁, saved.context.member⟩ nc) 54,
      ∃ θ : Env (rt_model_l (M := smdl_structure_l I (R := W) next.2.1) ⟨C₁, saved.context.member⟩ nc) 17,
        Tg_saved_code_d C W (η.bound 0).val V₁ r₁ (fun i => (ψ.bound i).val.val) ∧
        Formula.satisfies ψ tg_round0_m ∧ (∀ i, Rd_entry_d (v₀ i) (ψ.bound i).val.val j) ∧
        (∀ i, (θ.bound i).val = η.bound i) ∧ Formula.satisfies θ tg_subtype0_m ∧
        (∀ i : Fin 5, θ.bound ([0,1,2,5,9].get i) = ψ.bound ([16,24,15,13,11].get i)) ∧
        Formula.satisfies (θ.reindex (fun i : Fin 11 => [0,1,7,8,10,11,12,13,14,15,16].get i)) ts_numeric0_m

theorem Er_rank_cut_d.subtype_l
    {ω c X R c' Y S q Γ k N S₀ z c₁ wₚ ηₚ Cₚ Lₚ Vₚ rₚ Cᵣ qN wᵣ zᵣ : M.Domain}
    {v₀ : Fin 54 → M.Domain} (hω : M.IsOmega ω)
    (nx : ∃ x, M.mem x N) (hN : (smdl_structure_l I (R := S₀) nx).Models KP)
    (U₀ w ξ ℓ e β X' K' jN R' cN dN N' T' U u A₀ : (smdl_structure_l I (R := S₀) nx).Domain)
    (ground : (smdl_structure_l I (R := S₀) nx).Models ZF)
    (data : Er_rank_cut_d hZF ω c X R c' Y S q Γ k N S₀ z c₁ nx hN U₀ w ξ ℓ e β X' K' jN)
    (root : Zc_model_d I ω c X R)
    (owner : Smdl_d I c₁ N S₀) (fromRoot : Smap_d I ω c c₁ X N qN)
    (rootNumbers : Rr_layer_d I ω X R wᵣ zᵣ) (numbers : Rr_layer_d I ω N S₀ w.val z)
    (rootOld : Rd_entry_d Cᵣ Cₚ q)
    (D : (smdl_structure_l I (R := S₀) nx).Domain)
    (nd : Nonempty {x : (smdl_structure_l I (R := S₀) nx).Domain //
      (smdl_structure_l I (R := S₀) nx).mem x D})
    (transD : (smdl_structure_l I (R := S₀) nx).TransitiveSet D)
    (rootCurrent : Rd_entry_d Cᵣ D.val qN)
    (source : Ep_source_d (kp_pair_l hN) w ξ K' X' R')
    (mx : Smem_d (kp_pair_l hN) cN X' R') (my : Smem_d (kp_pair_l hN) dN N' T')
    (ultra : It_ultra_d (kp_pair_l hN) w ξ ℓ e cN dN jN)
    (ρ : Env (smdl_structure_l I (R := S₀) nx) 17)
    (hw : ρ.bound 0 = w)
    (hn : (smdl_structure_l I (R := S₀) nx).mem (ρ.bound 1) w)
    (hξ : (smdl_structure_l I (R := S₀) nx).mem ξ β)
    (hU : (smdl_structure_l I (R := S₀) nx).mem U β)
    (hu : (smdl_structure_l I (R := S₀) nx).mem u β)
    (hA : (smdl_structure_l I (R := S₀) nx).mem A₀ β)
    (names : Tn_names_d (ρ.bound 1) U A₀)
    (iξ : Rd_entry_d (M := smdl_structure_l I (R := S₀) nx) ξ (ρ.bound 2) jN)
    (iU : Rd_entry_d (M := smdl_structure_l I (R := S₀) nx) U (ρ.bound 5) jN)
    (iu : Rd_entry_d (M := smdl_structure_l I (R := S₀) nx) u (ρ.bound 9) jN)
    (program : ∀ j : Fin 9, (smdl_structure_l I (R := S₀) nx).mem
      (ρ.bound ([7,8,10,11,12,13,14,15,16].get j)) w)
    (π : Env (rt_model_l D nd) 11) (compiled : Formula.satisfies π ts_numeric0_m)
    (coordinates : ∀ i : Fin 11, (π.bound i).val = ρ.bound ([0,1,7,8,10,11,12,13,14,15,16].get i))
    (valid : Formula.satisfies ρ tg_subtype0_m)
    (parent : Smdl_d I c' Y S) (old : Tg_saved_d I wₚ Y S ηₚ Cₚ Lₚ Vₚ rₚ)
    (code : Tg_saved_code_d Y S wₚ Vₚ rₚ v₀)
    (links : ∀ i : Fin 5, Rd_entry_d ([w,ρ.bound 1,ξ,U,u].get i).val (v₀ ([16,24,15,13,11].get i)) k) :
    Er_subtype_d hZF ω c X R c' Y S q Γ k N S₀ z c₁ nx hN U₀ w ξ ℓ e β X' K' jN U u ρ
      wₚ ηₚ Cₚ Lₚ Vₚ rₚ v₀ := by
  obtain ⟨L, J, O, Z, A, p, T, V, r, o, C, W, j, q', p₀, data⟩ := data
  have saved := data
  obtain ⟨finite, _, carrier, hβU, _, transβ, _, _, _, _, _, _, _, _, _, embed, rootMap, _, agreement, _, _, certificate, rootGraph,
    _, _, _, _, _, _, _, _, _, _, _, _, rest⟩ := data
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rest⟩ := rest
  obtain ⟨_cD, _RD, _cut, _, _, _, _, _, _, _zD, _, _, _, rest⟩ := rest
  obtain ⟨w₀, w₁, _z₀, z₁, hww₀, _hww₁, omegaEdge, _oldNumbers, newNumbers, oldGraph, _newGraph, numeric,
    _sequences, _countableImage, _application, _representations, _closed, _collapse, _functions, _codes, _, _build⟩ := rest
  obtain ⟨hwβ,iω,inatural,next,_,_,_,_,_,_,_,_,_,_,_,_,_,_,
    A₁,Q₁,Y₁,e₁,D₁,Γ₁,t,owned,domain₁,carrier₁,ft,_,_,_,present,
    pred,commute,η,images,result⟩ :=
    saved.subtype_native_l hZF hω root nx hN ground source mx my ultra ρ hw hn hU hu hA names iU iu program valid
  let N₀ := smdl_structure_l I (R := S₀) nx
  let C₀ := smdl_structure_l I (R := W) next.2.1
  have targetZF : C₀.Models ZF := ZFC.models_zf_l ((certificate root).native_l I hZF hω)
  have hc := ZF.modelsKP targetZF
  have hj := ultra.elementary_l ground mx.1 my.1
  have nt := ultra.transitive_l ground my.1
  have natural := hj.natural_l ground source.omega source.transitive nt mx my source.omega_mem
  have carry (x : N₀.Domain) (i : Fin 17) a (hx : N₀.mem x β)
      (hi : Rd_entry_d x (ρ.bound i) jN) (ha : Rd_entry_d x.val a k) : Rd_entry_d a (η.bound i).val j :=
    (commute x (ρ.bound i) a (η.bound i).val hx hi ha).mp (images i)
  have coupled : ∀ i : Fin 5, Rd_entry_d (v₀ ([16,24,15,13,11].get i))
      (η.bound ([0,1,2,5,9].get i)).val j :=
    Fin.cases (carry w 0 _ hwβ (by rw [hw]; exact iω) (links 0))
      (Fin.cases (carry (ρ.bound 1) 1 _ (transβ w hwβ _ hn) inatural (links 1))
        (Fin.cases (carry ξ 2 _ hξ iξ (links 2))
          (Fin.cases (carry U 5 _ hU iU (links 3))
            (Fin.cases (carry u 9 _ hu iu (links 4)) (fun i => Fin.elim0 i)))))
  have eq₀ : w₀ = v₀ 16 := agreement.injection.1.1.2 w.val w₀ (v₀ 16) hww₀ (links 0)
  have eq₁ : (η.bound 0).val = w₁ := embed.1.1.1.2 _ _ _ (coupled 0) (eq₀ ▸ omegaEdge)
  have omega : C₀.IsOmega (η.bound 0) :=
    (show η.bound 0 = (⟨w₁, newNumbers.member⟩ : C₀.Domain) from Subtype.ext eq₁).symm ▸
      newNumbers.omega_l I (ZF.modelsKP hZF) hω hc.1
  have wp : Rd_entry_d w.val (η.bound 0).val t := (congrArg Subtype.val hw) ▸ images 0
  have lift_nat i (hi : N₀.mem (ρ.bound i) w) : C₀.mem (η.bound i) (η.bound 0) :=
    (pred w.val (η.bound 0).val wp _).mpr ⟨_, hi, images i⟩
  have resumed := old.subtype_image_l hZF code hω parent next embed targetZF η omega (lift_nat 1 hn)
    (fun i => lift_nat _ (program i)) coupled result
  obtain ⟨η₁, C₁, L₁, V₁, r₁, iw₁, iη, iC, iL, iV, ir, restored, nc, ψ, θ,
    row, round, archiveImages, same, subtype', links'⟩ := resumed
  let indices : Fin 11 → Fin 17 := fun i => [0,1,7,8,10,11,12,13,14,15,16].get i
  have low : ∀ i : Fin 11, ρ.bound (indices i) = w ∨ N₀.mem (ρ.bound (indices i)) w :=
    Fin.cases (Or.inl hw) (Fin.cases (Or.inr hn)
      (Fin.cases (Or.inr (program 0)) (Fin.cases (Or.inr (program 1))
        (Fin.cases (Or.inr (program 2)) (Fin.cases (Or.inr (program 3))
          (Fin.cases (Or.inr (program 4)) (Fin.cases (Or.inr (program 5))
            (Fin.cases (Or.inr (program 6)) (Fin.cases (Or.inr (program 7))
              (Fin.cases (Or.inr (program 8)) (fun i => Fin.elim0 i)))))))))))
  -- 同一常值方块识别全部内部自然数，不能只核对外部标准数。
  have values i : ((π.bound i).val.val = w.val ∧ ((θ.reindex indices).bound i).val.val = w₁) ∨
      ∃ a, Rd_entry_d a (π.bound i).val.val z ∧
        Rd_entry_d a ((θ.reindex indices).bound i).val.val z₁ := by
    have src := congrArg Subtype.val (coordinates i)
    have dst := congrArg Subtype.val (same (indices i))
    rcases low i with eq | hi
    · have image := (congrArg Subtype.val eq) ▸ images (indices i)
      exact Or.inl ⟨src.trans (congrArg Subtype.val eq),
        dst.trans ((ft.1.1.2 _ _ _ image wp).trans eq₁)⟩
    · obtain ⟨a, _, hax⟩ := (numbers.image (ρ.bound (indices i)).val).mp hi
      have hxβ := transβ w hwβ _ hi
      obtain ⟨b, _, hxb⟩ := agreement.injection.1.2.2 (ρ.bound (indices i)).val
        ((carrier _).mpr ⟨(ρ.bound (indices i)).property, finite.transitive β hβU _ hxβ⟩)
      have hab := (oldGraph a b).mpr ⟨_, hax, hxb⟩
      have hby := carry (ρ.bound (indices i)) (indices i) b hxβ (natural _ hi) hxb
      exact Or.inr ⟨a, src.symm ▸ hax, dst.symm ▸ (numeric a b hab _).mpr hby⟩
  have targetRoot : Rd_entry_d Cᵣ C₁ q' :=
    (rootGraph Cᵣ C₁).mpr ⟨fromRoot.1.1.input_mem_of_pairMember rootCurrent, Cₚ, rootOld, iC⟩
  have fs := restored.context.finite_l next.2.1 hc.1
  have compiled' := (smap_numeric_slice_peer_l hZF hω root.model owner next fromRoot rootMap
    root.ext (fromRoot.extensional_l hZF hω root.model owner root.ext) (certificate root).ext
    rootNumbers numbers newNumbers D ⟨C₁, restored.context.member⟩ transD fs.transitive nd nc
    rootCurrent targetRoot ts_numeric0_m ts_numeric0_closed_l π (θ.reindex indices) values).mp compiled
  exact ⟨hw, hn, hwβ, hξ, hU, hu, iω, inatural, iξ, iU, iu, program,
    parent, old, code, links,
    L, J, O, Z, A, p, T, V, r, o, C, W, j, q', p₀, saved, next,
    A₁, Q₁, Y₁, e₁, D₁, Γ₁, t, owned, domain₁, carrier₁, ft, present, pred, commute, η, images, result,
    η₁, C₁, L₁, V₁, r₁, iw₁, iη, iC, iL, iV, ir, restored, nc, ψ, θ,
    row, round, archiveImages, same, subtype', links', compiled'⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 同一次原继续选择生成原生后继

消费原更新核的完整结果，将其高支撑扩展器施加到实际较早源。
旧类型的切片范围由原输入推出，完整 subtype 沿同一代表池进入实际原后继。
两个查询池、χ∈L 及固定到该后继的完整工厂证书一并返回。
同一原边搬运完整旧存档，再把已经核对坐标的 subtype 放回其目标反射层。
同一 seed 的完整数值程序经共同原根传入该层，元数使用当前 subtype 的旧元数。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

/-- 同一次继续选择的全部原生扩展器、查询池及固定后继证书。 -/
def Tg_continue_raw_d (hZF : M.Models ZF) (ω c X R c' Y S q Γ k N S₀ z c₁ : M.Domain)
    (nx : ∃ x, M.mem x N) (hN : (smdl_structure_l (kp_pair_l (ZF.modelsKP hZF)) (R := S₀) nx).Models KP)
    (U₀ w β : (smdl_structure_l (kp_pair_l (ZF.modelsKP hZF)) (R := S₀) nx).Domain)
    (p : Fin 29 → (smdl_structure_l (kp_pair_l (ZF.modelsKP hZF)) (R := S₀) nx).Domain)
    (wₚ ηₚ Cₚ Lₚ Vₚ rₚ : M.Domain) (v : Fin 54 → M.Domain) : Prop :=
  let N₀ := smdl_structure_l (kp_pair_l (ZF.modelsKP hZF)) (R := S₀) nx
  let J := kp_pair_l hN
  let σ : Fin 7 → N₀.Domain := Fin.cases (p 21) (Fin.cases (p 22) (Fin.cases (p 23) (Fin.cases (p 24)
    (Fin.cases (p 25) (Fin.cases (p 26) (fun _ => p 27))))))
  ∃ X' K' R' L F cN dN N' T' jN θ U' D' u' : N₀.Domain,
    let ζ : Env N₀ 17 := ⟨fun i => [w,p 3,θ,p 8,p 9,U',p 13,p 14,p 16,u',
      p 21,p 22,p 23,p 24,p 25,p 26,p 27].get i, fun _ => w⟩
    V_d J (p 2) X' ∧ Ep_source_d J w (p 1) K' X' R' ∧
    N₀.mem L (p 2) ∧ N₀.mem (p 1) L ∧ N₀.mem (p 8) L ∧ N₀.mem (p 28) L ∧
    It_local_d J w X' R' (p 1) L F ∧ Sc_inaccessible_d w X' L ∧ Ex_strength_d J w (p 1) L X' F ∧
    Smem_d J cN X' R' ∧ Smem_d J dN N' T' ∧ It_ultra_d J w (p 1) L F cN dN jN ∧
    Wd_crit_d J X' jN (p 1) θ ∧ N₀.MemberSubset L θ ∧ N₀.IsLimitOrdinal θ ∧
    Rd_entry_d (M := N₀) (p 5) U' jN ∧ Rd_entry_d (M := N₀) (p 6) D' jN ∧ Rd_entry_d (M := N₀) (p 7) u' jN ∧
    Tt_pool_d J w (p 3) U' D' ∧ Ts_subtype_d (M := N₀) w (p 3) θ (p 8) (p 9) U' (p 13) (p 14) σ (p 16) u' ∧
    N₀.mem (p 9) w ∧ Tt_pool_d J w (p 9) (p 11) (p 12) ∧
    N₀.mem (p 3) w ∧ N₀.mem (p 5) β ∧ N₀.mem (p 6) β ∧ N₀.mem (p 7) β ∧
    (∀ j : Fin 9, N₀.mem (p ([14,16,21,22,23,24,25,26,27].get j)) w) ∧
    (∃ A : N₀.Domain, N₀.mem A β ∧ Tn_names_d (p 3) (p 5) A) ∧
    Er_subtype_d hZF ω c X R c' Y S q Γ k N S₀ z c₁ nx hN U₀ w (p 1) L F β X' K' jN (p 5) (p 7) ζ
      wₚ ηₚ Cₚ Lₚ Vₚ rₚ v

variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_context_d.raw_continue_l {ω c₁ N S₀ : M.Domain}
    (hω : M.IsOmega ω) (nx : ∃ x, M.mem x N) :
    let N₀ := smdl_structure_l I (R := S₀) nx
    ∀ ground : N₀.Models ZFC,
    let hN := ZF.modelsKP (ZFC.models_zf_l ground)
    let J := kp_pair_l hN
    ∀ U₀ w η C α β ζ : N₀.Domain,
    ∀ nc : Nonempty {x : N₀.Domain // N₀.mem x C}, ∀ ρ : Env (rt_model_l (M := N₀) C nc) 29,
    let p := fun i : Fin 29 => (ρ.bound i).val
    ∀ {c X R c' Y S q Γ H k z wₚ ηₚ Cₚ Lₚ Vₚ rₚ Cᵣ qN wᵣ zᵣ : M.Domain}, ∀ v : Fin 54 → M.Domain,
    Tg_context_d I w.val N S₀ η.val C.val → Smdl_d I c₁ N S₀ →
    Zc_model_d I ω c X R → Smdl_d I c' Y S → Smap_d I ω c c' X Y q →
    Smap_d I ω c c₁ X N qN → Rr_layer_d I ω X R wᵣ zᵣ →
    Rd_entry_d Cᵣ Cₚ q → Rd_entry_d Cᵣ C.val qN →
    Tg_saved_d I wₚ Y S ηₚ Cₚ Lₚ Vₚ rₚ → Tg_saved_code_d Y S wₚ Vₚ rₚ v →
    (∀ i : Fin 5, Rd_entry_d ([w,p 3,p 1,p 5,p 7].get i).val (v ([16,24,15,13,11].get i)) k) →
    Rr_layer_d I ω N S₀ w.val z → V_d J ζ U₀ → N₀.IsLimitOrdinal ζ →
    (∀ x, M.mem x Γ ↔ M.mem x N ∧ Rd_entry_d x U₀.val S₀) →
    M.IsSetInjectionFromTo I k Γ Y →
    (∀ y, Rd_entry_d y H S ↔ ∃ x, M.mem x Γ ∧ Rd_entry_d x y k) →
    (∀ x y, Rd_entry_d x y k → ∀ t, Rd_entry_d t y S ↔ ∃ d, Rd_entry_d d x S₀ ∧ Rd_entry_d d t k) →
    Rr_closed_d I Y S H → Rr_small_d I Y S H → N₀.mem β U₀ → N₀.mem (p 1) β →
    N₀.IsLimitOrdinal α → V_d J α β → N₀.MemberSubset α (p 8) →
    p 0 = w → N₀.IsRegularCardinal J (p 2) →
    Formula.satisfies ρ tc_seed0_m → Formula.satisfies ρ tc_result0_m →
    Tg_continue_raw_d hZF ω c X R c' Y S q Γ k N S₀ z c₁ nx hN U₀ w β p wₚ ηₚ Cₚ Lₚ Vₚ rₚ v := by
  intro N₀ ground hN J U₀ w η C α β ζ nc ρ p
  let σ : Fin 7 → N₀.Domain := Fin.cases (p 21) (Fin.cases (p 22) (Fin.cases (p 23) (Fin.cases (p 24)
    (Fin.cases (p 25) (Fin.cases (p 26) (fun _ => p 27))))))
  intro c X R c' Y S q Γ H k z wₚ ηₚ Cₚ Lₚ Vₚ rₚ Cᵣ qN wᵣ zᵣ v context owner root model hq
    fromRoot rootNumbers rootOld rootCurrent prior code oldLinks
    numbers rank₀ limit₀ carrier fk image pred closed small
    hβ hκ ha rankB above hw regular seed valid
  have fs : Fs_read_d (M := N₀) w C := context.finite_l nx hN.1
  have nw := numbers.omega_l I (ZF.modelsKP hZF) hω hN.1
  have rankC : V_d J η C := (rr_rank_native_l I nx hN η C).mp ((rr_rank_truth_l I).mpr context.rank)
  obtain ⟨arity, sourceU, sourceD, sourceType, program, A₀, scopeA, names₀⟩ :=
    tc_seed_scope_l (ZFC.models_zf_l ground) nw rankC fs nc ρ hw rankB ha hκ seed
  simp only [tc_result0_m, Formula.satisfies_conj_iff] at valid
  obtain ⟨chosen, finite, currentPool⟩ := valid
  have full := tc_image_absolute_l ground nw rankC fs nc ρ
    (.bound 0) _ (.bound 2) _ _ _ _ _ _ _ _ _ _ _ hw regular chosen
  have full := (tc_image_sat_l hN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).mp full
  simp only [@eval_image_env_l (rt_model_l (M := N₀) C nc) N₀ Subtype.val, Term.eval_bound] at full
  change (ρ.bound 0).val = w at hw
  simp only [hw] at full
  obtain ⟨X', K', R', L, F, cN, dN, N', T', jN, θ, U', D', u',
    ⟨rank, source, hLδ, hκL, hτL, loc, card, strong, mx, my, ultra, crit, bound, limit, hU, hD, hu⟩,
    high, pool, subtype⟩ := full
  obtain ⟨A, E, _, _, names, seq, product⟩ :=
    (fs.pool_sat_l hN nc ρ (.bound 0) (.bound 9) (.bound 11) (.bound 12) hw).mp currentPool
  have finite : N₀.mem (p 9) w := hw ▸ (Formula.satisfies_mem_iff ..).mp finite
  have hαL := ordinal_down_l hN ha.1 (loc.ordinals_l hN source.transitive source.code).2 above hτL
  have step := loc.raw_rank_source_l hZFC hω nx ground
    U₀ w (p 1) L F α β ζ X' K' R' (p 2) cN dN N' T' jN θ
    owner root model hq numbers rank₀ limit₀ carrier fk image pred closed small hβ hκ ha rankB hαL
    source rank regular.isLimitOrdinal mx my ultra card strong crit.image bound
  let f : Fin 7 → Term 29 := Fin.cases (.bound 21) (Fin.cases (.bound 22) (Fin.cases (.bound 23)
    (Fin.cases (.bound 24) (Fin.cases (.bound 25) (Fin.cases (.bound 26) (fun _ => .bound 27))))))
  have slots : (fun i => ((f i).eval ρ).val) = σ := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))))) i
  have subtype : Ts_subtype_d (M := N₀) w (p 3) θ (p 8) (p 9) U' (p 13) (p 14) σ (p 16) u' := slots ▸ subtype
  let ε : Env N₀ 17 := ⟨fun i => [w,p 3,θ,p 8,p 9,U',p 13,p 14,p 16,u',
    p 21,p 22,p 23,p 24,p 25,p 26,p 27].get i, fun _ => w⟩
  let g : Fin 7 → Term 17 := Fin.cases (.bound 10) (Fin.cases (.bound 11) (Fin.cases (.bound 12)
    (Fin.cases (.bound 13) (Fin.cases (.bound 14) (Fin.cases (.bound 15) (fun _ => .bound 16))))))
  have codes : (fun i => (g i).eval ε) = σ := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))))) i
  have valid : Formula.satisfies ε tg_subtype0_m := by
    apply (ts_subtype_sat_l hN ε (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4)
      (.bound 5) (.bound 6) (.bound 7) (.bound 8) (.bound 9) g).mpr
    rw [codes]
    exact subtype
  have programs : ∀ j : Fin 9, N₀.mem (ε.bound ([7,8,10,11,12,13,14,15,16].get j)) w :=
    Fin.cases (program 0) (Fin.cases (program 1) (Fin.cases (program 2) (Fin.cases (program 3)
      (Fin.cases (program 4) (Fin.cases (program 5) (Fin.cases (program 6)
        (Fin.cases (program 7) (Fin.cases (program 8) (fun j => Fin.elim0 j)))))))))
  -- 保留实际 seed 的完整编译证书，文本在数值公式中存在量化。
  let π : Env (rt_model_l (M := N₀) C nc) 11 :=
    ρ.reindex (fun i => [0,3,14,16,21,22,23,24,25,26,27].get i)
  have compiled : Formula.satisfies π ts_numeric0_m := by
    have facts := seed
    simp only [tc_seed0_m, Formula.satisfies_conj_iff] at facts
    have original := facts.2.1
    simp only [ts_numeric0_m, Formula.satisfies_exists_iff]
    refine ⟨ρ.bound 15, ?_⟩
    simp only [ts_program_m, Formula.satisfies_bind] at original ⊢
    apply (Formula.closed_env_l ts_program0_m ts_program0_closed_l ?_).mp original
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)))))))))))) i
  have coordinates : ∀ i : Fin 11, (π.bound i).val = ε.bound ([0,1,7,8,10,11,12,13,14,15,16].get i) :=
    Fin.cases hw (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (fun j => Fin.elim0 j)))))))))))
  have target := Er_rank_cut_d.subtype_l hZF hω nx hN
    U₀ w (p 1) L F β X' K' jN R' cN dN N' T' (p 5) (p 7) A₀ (ZFC.models_zf_l ground)
    step root owner fromRoot rootNumbers numbers rootOld C nc fs.transitive rootCurrent
    source mx my ultra ε rfl arity hκ sourceU sourceType scopeA names₀ crit.image hU hu
    programs π compiled coordinates valid
    model prior code oldLinks
  exact ⟨X', K', R', L, F, cN, dN, N', T', jN, θ, U', D', u',
    rank, source, hLδ, hκL, hτL, high, loc, card, strong, mx, my, ultra, crit, bound, limit, hU, hD, hu,
    pool, subtype, finite, ⟨A, E, names, seq, product⟩,
    arity, sourceU, sourceD, sourceType, program, ⟨A₀, scopeA, names₀⟩, target⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 同一档案行的完整准备与两步复制结果

源行和当前树框架保留实际对象码。语言、逆图、继续选择、严格切片、
原工厂及完整两步复制合成一个结论，供整列选行后直接调用。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Tg_prepared_d
    (ω T E m QT GT c₀ X₀ R₀ N S B σ d q C₀ S₀ w' η' C' zn χ γ₀ Bγ
      i c X R w η C L U r p A π o n Q G Λ H : M.Domain)
    (mn : Smdl_d I d N S) (hN : (smdl_structure_l I (R := S) mn.2.1).Models KP)
    (current : Tg_context_d I w' N S η' C')
    (ncN : Nonempty {x : (smdl_structure_l I (R := S) mn.2.1).Domain //
      (smdl_structure_l I (R := S) mn.2.1).mem x ⟨C',current.member⟩})
    (ι : Env (rt_model_l (M := smdl_structure_l I (R := S) mn.2.1) ⟨C',current.member⟩ ncN) 46)
    (hω : M.IsOmega ω) : Prop :=
    ∃ v : Fin 54 → M.Domain, Tg_saved_code_d X R w U r v ∧
      Tg_record_d I w X R η C (v 15) (v 18) r ∧
    ∃ l φ V Γ t, ∃ same : Ic_agree_d I X R A π N S B σ L l φ U V Γ t,
      Rr_truth_d I N S (Formula.isLimitOrdinal .newest) (fun _ : Fin 1 => l) ∧ Rd_entry_d V C' S ∧
    ∃ D k, (∀ x, M.mem x D ↔ M.mem x N ∧ Rd_entry_d x V S) ∧
      M.IsSetInjectionFromTo I k D X ∧
      (∀ y, Rd_entry_d y U R ↔ ∃ x, M.mem x D ∧ Rd_entry_d x y k) ∧
      (∀ x y, Rd_entry_d x y k → ∀ z, Rd_entry_d z y R ↔ ∃ a, Rd_entry_d a x S ∧ Rd_entry_d a z k) ∧
      (∀ x y, Rd_entry_d x y k ↔ Rd_entry_d y x t) ∧
      (∀ x x' y, Rd_entry_d x x' σ → Rd_entry_d x y k → Rd_entry_d y x' π) ∧
    ∃ nd : Nonempty {x : (smdl_structure_l I (R := S) mn.2.1).Domain //
      (smdl_structure_l I (R := S) mn.2.1).mem x ⟨C', current.member⟩},
    ∃ θ : Env (rt_model_l (M := smdl_structure_l I (R := S) mn.2.1) ⟨C', current.member⟩ nd) 10,
      (∀ j : Fin 10, Rd_entry_d (θ.bound j).val.val (v ([16,15,24,14,13,12,6,5,4,3].get j)) k) ∧
      (θ.bound 0).val.val = w' ∧ Rd_entry_d (θ.bound 1).val.val V S ∧ Formula.satisfies θ ee_language0_m ∧
      ∃ a : (rt_model_l (M := smdl_structure_l I (R := S) mn.2.1) ⟨C', current.member⟩ nd).Domain,
        Rd_entry_d a.val.val (v 11) k ∧
        Formula.satisfies (θ.push a) (ee_elastic_m (.bound 7) (.bound 8) (.bound 9) (.bound 10) .newest) ∧
      ∃ ζ : Env (rt_model_l (M := smdl_structure_l I (R := S) mn.2.1) ⟨C', current.member⟩ nd) 3,
        (∀ j : Fin 3, Rd_entry_d (ζ.bound j).val.val (v ([41,22,23].get j)) k) ∧
        Fn0_d (M := smdl_structure_l I (R := S) mn.2.1) (ζ.bound 1).val (θ.bound 0).val (ζ.bound 0).val ∧
        (smdl_structure_l I (R := S) mn.2.1).SuccessorOf (ζ.bound 2).val (ζ.bound 1).val ∧
        (smdl_structure_l I (R := S) mn.2.1).SuccessorOf (θ.bound 2).val (ζ.bound 2).val ∧
      ∃ ε : Env (rt_model_l (M := smdl_structure_l I (R := S) mn.2.1) ⟨C', current.member⟩ nd) 7,
        Formula.satisfies ε tg_reply_base0_m ∧
        (∀ j : Fin 7, Rd_entry_d (ε.bound j).val.val (v ([16,17,23,24,2,1,0].get j)) k) ∧
        ε.bound 0 = θ.bound 0 ∧ ε.bound 3 = θ.bound 2 ∧
        (smdl_structure_l I (R := S) mn.2.1).mem (ε.bound 2).val (θ.bound 2).val ∧
        (smdl_structure_l I (R := S) mn.2.1).mem (ε.bound 6).val a.val ∧
        (∀ x : (smdl_structure_l I (R := S) mn.2.1).Domain,
          ¬ (smdl_structure_l I (R := S) mn.2.1).mem x (ε.bound 1).val) ∧
      ∃ ν : Env (rt_model_l (M := smdl_structure_l I (R := S) mn.2.1) ⟨C',current.member⟩ nd) 29,
        Formula.satisfies ν tc_seed0_m ∧ Formula.satisfies ν tc_result0_m ∧
        (∀ j : Fin 10, ν.bound ([0,1,3,4,5,6,17,18,19,20].get j) = θ.bound j) ∧
        ν.bound 7 = a ∧ ν.bound 3 = ι.bound 27 ∧
        (∀ j : Fin 14, ν.bound ([0,2,8,9,13,14,16,21,22,23,24,25,26,27].get j) =
          ι.bound ([0,5,24,28,25,36,37,38,39,40,41,42,43,44].get j)) ∧
        (smdl_structure_l I (R := S) mn.2.1).MemberSubset (ζ.bound 0).val (ι.bound 23).val ∧
        (ν.bound 28).val.val = χ ∧
        It_lower_d I γ₀ N S (ν.bound 1).val.val ∧
        ∃ αc βc : (smdl_structure_l I (R := S) mn.2.1).Domain,
          Rd_entry_d αc.val l S ∧ Rd_entry_d βc.val V S ∧
          (smdl_structure_l I (R := S) mn.2.1).mem (ν.bound 1).val βc ∧
          (smdl_structure_l I (R := S) mn.2.1).IsLimitOrdinal αc ∧ V_d (kp_pair_l hN) αc βc ∧
          (smdl_structure_l I (R := S) mn.2.1).MemberSubset αc (ν.bound 8).val ∧
          Tg_continue_raw_d hZF ω c₀ X₀ R₀ c X R p D k N S zn d mn.2.1 hN
            ⟨V,same.common.right_rank.2.1⟩ ⟨w',current.omega_mem⟩ βc
            (fun j => (ν.bound j).val) w η C L U r v ∧
          ∃ Xc Kc jc ℓ e ec : (smdl_structure_l I (R := S) mn.2.1).Domain,
          ∃ Ls Js Os Zs Ds ps Vs Ws qs d₁ N₁ S₁ j₁ q₁ p₁ D₁ t₁ w₁ η₁ C₁,
          ∃ restored : Tg_context_d I w₁ N₁ S₁ η₁ C₁,
          ∃ nc₁ : Nonempty {x : (smdl_structure_l I (R := S₁) ⟨w₁,restored.omega_mem⟩).Domain //
            (smdl_structure_l I (R := S₁) ⟨w₁,restored.omega_mem⟩).mem x ⟨C₁,restored.member⟩},
          ∃ ρ₁ : Env (rt_model_l (M := smdl_structure_l I (R := S₁) ⟨w₁,restored.omega_mem⟩)
            ⟨C₁,restored.member⟩ nc₁) 54,
          ∃ θ₁ : Env (rt_model_l (M := smdl_structure_l I (R := S₁) ⟨w₁,restored.omega_mem⟩)
            ⟨C₁,restored.member⟩ nc₁) 17,
            (∀ j, Rd_entry_d (v j) (ρ₁.bound j).val.val j₁) ∧
            Ic_two_step_d hZF ω c₀ X₀ R₀ c X R d N S p D k zn n m T Q G E Λ H QT GT i o B σ
              w η C (v 15) (v 18) r Ls Js Os Zs Ds ps Vs Ws qs d₁ N₁ S₁ j₁ q₁ p₁ q C₀ S₀ η' C' γ₀ Bγ D₁ t₁
              w₁ η₁ C₁ mn hN ⟨V,same.common.right_rank.2.1⟩ ⟨w',current.omega_mem⟩ (ν.bound 1).val
              ℓ e βc Xc Kc jc ec hω current nd ν ι restored nc₁ ρ₁ θ₁

end YesMetaZFC.SetTheory.LargeCardinal
