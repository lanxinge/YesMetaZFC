import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawAlphabet
import YesMetaZFC.SetTheory.LargeCardinal.Game.Subtype
import YesMetaZFC.Model.SetTheory.Relations.NativeSmemSlice

/-! # 固定原施加的完整代表池输运 subtype

先用同一常值方块把旧常量域、类型及名字域的超幂像放入完整池，
再沿池的完整同构传输查询。结论固定原施加的后继和父边，并保留
全部十七个参数的像；不依赖普通游戏或 demanding 游戏的存档格式。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Er_rank_cut_at_d.subtype_native_l
    {ω c X R c' Y S q Γ k N S₀ z c₁ L J O Z A p T V r o C W j q' p₀ : M.Domain}
    (hω : M.IsOmega ω) (root : Zc_model_d I ω c X R)
    (nx : ∃ x, M.mem x N) (hN : (smdl_structure_l I (R := S₀) nx).Models KP)
    (ground : (smdl_structure_l I (R := S₀) nx).Models ZF)
    {U₀ w ξ ℓ e β X' K' jN R' cN dN N' T' U u A₀ :
      (smdl_structure_l I (R := S₀) nx).Domain}
    (data : Er_rank_cut_at_d hZF ω c X R c' Y S q Γ k N S₀ z c₁ nx hN
      U₀ w ξ ℓ e β X' K' jN L J O Z A p T V r o C W j q' p₀)
    (source : Ep_source_d (kp_pair_l hN) w ξ K' X' R')
    (mx : Smem_d (kp_pair_l hN) cN X' R') (my : Smem_d (kp_pair_l hN) dN N' T')
    (ultra : It_ultra_d (kp_pair_l hN) w ξ ℓ e cN dN jN)
    (ρ : Env (smdl_structure_l I (R := S₀) nx) 17) (hw : ρ.bound 0 = w)
    (hn : (smdl_structure_l I (R := S₀) nx).mem (ρ.bound 1) w)
    (hU : (smdl_structure_l I (R := S₀) nx).mem U β)
    (hu : (smdl_structure_l I (R := S₀) nx).mem u β)
    (hA : (smdl_structure_l I (R := S₀) nx).mem A₀ β)
    (names : Tn_names_d (ρ.bound 1) U A₀)
    (iU : Rd_entry_d U (ρ.bound 5) jN) (iu : Rd_entry_d u (ρ.bound 9) jN)
    (program : ∀ i : Fin 9, (smdl_structure_l I (R := S₀) nx).mem
      (ρ.bound ([7,8,10,11,12,13,14,15,16].get i)) w)
    (valid : Formula.satisfies ρ tg_subtype0_m) :
    (smdl_structure_l I (R := S₀) nx).mem w β ∧ Rd_entry_d w w jN ∧
      Rd_entry_d (ρ.bound 1) (ρ.bound 1) jN ∧
    ∃ next : Smdl_d I o C W,
    ∃ Uc : (smdl_structure_l I (R := S₀) nx).Domain, ∃ lc Vc Δc gc,
      Ic_common_d I N S₀ C W ℓ.val lc Uc.val Vc Δc gc ∧
    ∃ Kc : (smdl_structure_l I (R := S₀) nx).Domain, ∃ bκ κc,
      V_d (kp_pair_l hN) ξ Kc ∧
      (∀ x : (smdl_structure_l I (R := S₀) nx).Domain, ∀ b E,
        (smdl_structure_l I (R := S₀) nx).mem x Kc → Rd_entry_d x.val b k →
          (Rd_entry_d x.val E gc ↔ Rd_entry_d b E j)) ∧
      Rd_entry_d ξ.val bκ k ∧ Rd_entry_d bκ κc j ∧
      (∀ E, Rd_entry_d E lc W → Rd_entry_d E κc W) ∧
    ∃ A₁ Q₁ Y₁ e₁ : (smdl_structure_l I (R := S₀) nx).Domain, ∃ D₁ Γ₁ t,
      Eb_collapse_d w ξ ℓ K' X' β e A₁ Q₁ Y₁ e₁ ∧
      (∀ x, M.mem x D₁ ↔ M.mem x N ∧ Rd_entry_d x A₁.val S₀) ∧
      (∀ x, M.mem x Γ₁ ↔ M.mem x N ∧ Rd_entry_d x Y₁.val S₀) ∧
      M.IsSetInjectionFromTo I t Γ₁ C ∧ M.IsRestrictionOf I gc t Δc ∧
      Rd_entry_d ℓ.val lc t ∧ Rd_entry_d Uc.val Vc t ∧
      Er_present_d I ω L N S₀ z Γ Y k r e₁.val D₁ t ∧
      (∀ x E, Rd_entry_d x E t → ∀ P,
        Rd_entry_d P E W ↔ ∃ y, Rd_entry_d y x S₀ ∧ Rd_entry_d y P t) ∧
      (∀ x y : (smdl_structure_l I (R := S₀) nx).Domain, ∀ b E,
        (smdl_structure_l I (R := S₀) nx).mem x β → Rd_entry_d x y jN →
        Rd_entry_d x.val b k → (Rd_entry_d y.val E t ↔ Rd_entry_d b E j)) ∧
    ∃ η : Env (smdl_structure_l I (R := W) next.2.1) 17,
      (∀ i, Rd_entry_d (ρ.bound i).val (η.bound i).val t) ∧ Formula.satisfies η tg_subtype0_m := by
  obtain ⟨finite,_,carrier,hβU,hβX,transβ,_,_,_,_,_,next,_,_,_,embed,_,_,agreement,_,_,certificate,
    _,Uc,_,_,_,_,lc,Vc,Δc,gc,common,_,_,rest⟩ := data
  obtain ⟨Kc,rankKc,square,_,bκ,κc,_,iκ,κj,_,cap,_,_,_,_,_,_,_,_,rest⟩ := rest
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,rest⟩ := rest
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,pool,_⟩ := rest
  obtain ⟨A₁,Q₁,Y₁,e₁,D₁,Γ₁,_,_,t,owned,domain₁,carrier₁,_,_,_,_,ft,restrict,endpoint,layer,present,_,
    _,Hβ,_,hbH,full,pred,commute,_⟩ := pool
  let N₀ := smdl_structure_l I (R := S₀) nx
  let C₀ := smdl_structure_l I (R := W) next.2.1
  have hc := ZF.modelsKP (ZFC.models_zf_l ((certificate root).native_l I hZF hω))
  have owned' := owned
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,collapse,_⟩ := owned'
  have yt : N₀.TransitiveSet Y₁ := collapse.transitive
  -- 常值方块保证所有需要的超幂像属于这一次施加的完整池。
  have inside (x y : N₀.Domain) (hx : N₀.mem x β) (hxy : Rd_entry_d x y jN) : N₀.mem y Y₁ := by
    obtain ⟨b,_,hxb⟩ := agreement.injection.1.2.2 x.val
      ((carrier x.val).mpr ⟨x.property,finite.transitive β hβU x hx⟩)
    obtain ⟨E,_,hbE⟩ := embed.1.1.2.2 b (agreement.injection.1.output_mem_of_pairMember hxb)
    exact ((carrier₁ y.val).mp (ft.1.input_mem_of_pairMember ((commute x y b E hx hxy hxb).mpr hbE))).2
  have hU₁ := inside U (ρ.bound 5) hU iU
  have hu₁ := inside u (ρ.bound 9) hu iu
  have hj := ultra.elementary_l ground mx.1 my.1
  have nt := ultra.transitive_l ground my.1
  obtain ⟨A',_,iA⟩ := hj.1.1.2.2 A₀ (source.transitive β hβX A₀ hA)
  have ha₁ := inside A₀ A' hA iA
  have natural := hj.natural_l ground source.omega source.transitive nt mx my source.omega_mem
  let a : Env N₀ 3 := ⟨fun i => [ρ.bound 1,U,A₀].get i,fun _ => w⟩
  let b : Env N₀ 3 := ⟨fun i => [ρ.bound 1,ρ.bound 5,A'].get i,fun _ => w⟩
  have moved := smap_delta_l (kp_pair_l hN) ground source.omega source.transitive nt mx my hj
    (tn_names0_m (.bound 0) (.bound 1) (.bound 2)) (by simp -implicitDefEqProofs) (tn_names0_delta_l ..) a b
    (Fin.cases (natural _ hn) (Fin.cases iU (Fin.cases iA (fun i => Fin.elim0 i))))
  have names' : Tn_names_d (ρ.bound 1) (ρ.bound 5) A' :=
    (tn_names0_sat_l hN b (.bound 0) (.bound 1) (.bound 2)).mp
      (moved.mp ((tn_names0_sat_l hN a (.bound 0) (.bound 1) (.bound 2)).mpr names))
  let slots : Fin 7 → Term 17 := Fin.cases (.bound 10) (Fin.cases (.bound 11) (Fin.cases (.bound 12)
    (Fin.cases (.bound 13) (Fin.cases (.bound 14) (Fin.cases (.bound 15) (fun _ => .bound 16))))))
  have subtype := (ts_subtype_sat_l hN ρ (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4)
    (.bound 5) (.bound 6) (.bound 7) (.bound 8) (.bound 9) slots).mp valid
  have facts := subtype
  obtain ⟨_,_,_,query,_⟩ := facts
  obtain ⟨hv,hm,hn₀,hτ,hκ,hw₀⟩ := query.constants
  have iω := hj.omega_l (kp_pair_l hN) ground source.omega source.transitive nt mx my source.omega_mem
  have hwU := (hj.member_l (kp_pair_l hN) ground source.omega mx my iω iU).mpr (hw ▸ hw₀)
  have hwβ := transβ U hU w hwU
  have low i (hi : N₀.mem (ρ.bound i) (ρ.bound 5)) := yt _ hU₁ _ hi
  have hwY : N₀.mem w Y₁ := hw ▸ low 0 hw₀
  have prog i := yt w hwY _ (program i)
  have members : ∀ i, N₀.mem (ρ.bound i) Y₁ := by
    simp only [Fin.forall_fin_succ]
    exact ⟨low 0 hw₀,low 1 hn₀,low 2 hκ,low 3 hτ,low 4 hm,hU₁,low 6 hv,
      prog 0,prog 1,hu₁,prog 2,prog 3,prog 4,prog 5,prog 6,prog 7,prog 8,fun i => Fin.elim0 i⟩
  let nu : Nonempty {x : N₀.Domain // N₀.mem x Y₁} := ⟨⟨ρ.bound 0,members 0⟩⟩
  let θ : Env (rt_model_l Y₁ nu) 17 := ⟨fun i => ⟨ρ.bound i,members i⟩,fun _ => ⟨ρ.bound 0,members 0⟩⟩
  have values : (fun i => ((slots i).eval θ).val) = (fun i => (slots i).eval ρ) := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))))) i
  have reflected : Formula.satisfies θ tg_subtype0_m :=
    ts_subtype_reflect_l hN yt nu θ (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4)
      (.bound 5) (.bound 6) (.bound 7) (.bound 8) (.bound 9) slots ha₁ names' (values.symm ▸ subtype)
  obtain ⟨v,hv⟩ := Classical.axiomOfChoice (fun i : Fin 17 => ft.1.2.2 (ρ.bound i).val
    ((carrier₁ _).mpr ⟨(ρ.bound i).property,members i⟩))
  let H : C₀.Domain := ⟨Hβ,embed.1.1.output_mem_of_pairMember hbH⟩
  have vh i : C₀.mem ⟨v i,(hv i).1⟩ H :=
    (full (v i)).mpr ⟨_,ft.1.input_mem_of_pairMember (hv i).2,(hv i).2⟩
  let nv : Nonempty {x : C₀.Domain // C₀.mem x H} := ⟨⟨⟨v 0,(hv 0).1⟩,vh 0⟩⟩
  let ε : Env (rt_model_l H nv) 17 := ⟨fun i => ⟨⟨v i,(hv i).1⟩,vh i⟩,fun _ => ⟨⟨v 0,(hv 0).1⟩,vh 0⟩⟩
  have ht : C₀.TransitiveSet H := by
    intro x hx y hy
    obtain ⟨a,_,hax⟩ := (full x.val).mp hx
    obtain ⟨b,_,hby⟩ := (pred a x.val hax y.val).mp hy
    exact (full y.val).mpr ⟨b,ft.1.input_mem_of_pairMember hby,hby⟩
  have transferred := (rr_native_slice_l I nx next.2.1 Y₁ H nu nv carrier₁ ft full pred
    tg_subtype0_m tg_subtype0_closed_l θ ε (fun i => (hv i).2)).mp reflected
  have actual := ts_subtype_source_l hc ht nv ε (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4)
    (.bound 5) (.bound 6) (.bound 7) (.bound 8) (.bound 9) slots transferred
  let η := image_env_l Subtype.val ε
  have result : Formula.satisfies η tg_subtype0_m := by
    apply (ts_subtype_sat_l hc η (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4)
      (.bound 5) (.bound 6) (.bound 7) (.bound 8) (.bound 9) slots).mpr
    simpa only [η,@eval_image_env_l (rt_model_l H nv) C₀ Subtype.val] using actual
  exact ⟨hwβ,iω,natural _ hn,next,Uc,lc,Vc,Δc,gc,common,
    Kc,bκ,κc,rankKc,square,iκ,κj,cap,
    A₁,Q₁,Y₁,e₁,D₁,Γ₁,t,owned,domain₁,carrier₁,ft,restrict,endpoint,layer,present,
    pred,commute,η,fun i => (hv i).2,result⟩

end YesMetaZFC.SetTheory.LargeCardinal
