import YesMetaZFC.SetTheory.LargeCardinal.Game.RawCritical
import YesMetaZFC.SetTheory.LargeCardinal.Game.RootSquare
import YesMetaZFC.Model.SetTheory.Relations.SliceEmbedding
import YesMetaZFC.SetTheory.LargeCardinal.Game.NativePlay

/-! # 原根切片上的完整查询回读

目标参数由实际切片满像取得共同根原像，再由源切片取得源参数。
两条根嵌入负责完整反射层中的公式；已保存的根方块只负责识别同一共同图。
原根切片可以非良基，不使用完整低层解释的外部唯一性。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 全模型真值只需目标切片满像和根方块；源参数由完整根嵌入生成。 -/
theorem Tg_root_slice_d.model_back_l
    {Ω b B R₀ c X R d Y S j k D₀ γ₀ C₀ C γ V s g : M.Domain}
    (target : Tg_root_slice_d I B R₀ γ₀ D₀ C₀ Y S C k γ V s)
    (square : Tg_root_square_d D₀ j k g)
    (hΩ : M.IsOmega Ω) (mb : Smdl_d I b B R₀) (mx : Smdl_d I c X R) (my : Smdl_d I d Y S)
    (left : Smap_d I Ω b c B X j) (right : Smap_d I Ω b d B Y k)
    {n} (φ : Formula 1 n) (closed : φ.FreeClosed)
    (θ : Env (smdl_structure_l I (R := S) my.2.1) n)
    (low : ∀ i, Rd_entry_d (θ.bound i).val V S) (valid : Formula.satisfies θ φ) :
    ∃ ρ : Env (smdl_structure_l I (R := R) mx.2.1) n,
      (∀ i, Rd_entry_d (ρ.bound i).val (θ.bound i).val g) ∧ Formula.satisfies ρ φ := by
  obtain ⟨a,ha⟩ := Classical.axiomOfChoice (fun i => (target.image _).mp (low i))
  have points i := target.root _ _ (ha i).2
  have members i := right.1.1.input_mem_of_pairMember (points i)
  obtain ⟨v,hv⟩ := Classical.axiomOfChoice (fun i => left.1.1.2.2 (a i) (members i))
  obtain ⟨e,he⟩ := mb.2.1
  obtain ⟨f,hf⟩ := mx.2.1
  let α : Env (smdl_structure_l I (R := R₀) mb.2.1) n :=
    ⟨fun i => ⟨a i,members i⟩,fun _ => ⟨e,he⟩⟩
  let ρ : Env (smdl_structure_l I (R := R) mx.2.1) n :=
    ⟨fun i => ⟨v i,(hv i).1⟩,fun _ => ⟨f,hf⟩⟩
  have root := (smap_source_l I hZF hΩ mb my right φ closed α θ points).mpr valid
  exact ⟨ρ,fun i => (square (a i) (ha i).1 _ (hv i).2 _).mpr (points i),
    (smap_source_l I hZF hΩ mb mx left φ closed α ρ (fun i => (hv i).2)).mp root⟩

/-- 同一根方块把目标低参数的整句真值送回原反射层，保留全部共同图坐标。 -/
theorem Tg_root_slice_d.back_l
    {Ω b B R₀ c X R d Y S j k D₀ γ₀ C₀ C C' γ V s γ' V' s' g : M.Domain}
    (source : Tg_root_slice_d I B R₀ γ₀ D₀ C₀ X R C j γ V s)
    (target : Tg_root_slice_d I B R₀ γ₀ D₀ C₀ Y S C' k γ' V' s')
    (square : Tg_root_square_d D₀ j k g)
    (hΩ : M.IsOmega Ω) (mb : Smdl_d I b B R₀) (mx : Smdl_d I c X R) (my : Smdl_d I d Y S)
    (left : Smap_d I Ω b c B X j) (right : Smap_d I Ω b d B Y k)
    (ct : (smdl_structure_l I (R := R) mx.2.1).TransitiveSet
      ⟨C,left.1.1.output_mem_of_pairMember source.context⟩)
    (dt : (smdl_structure_l I (R := S) my.2.1).TransitiveSet
      ⟨C',right.1.1.output_mem_of_pairMember target.context⟩)
    (nc : Nonempty {x : (smdl_structure_l I (R := R) mx.2.1).Domain //
      (smdl_structure_l I (R := R) mx.2.1).mem x ⟨C,left.1.1.output_mem_of_pairMember source.context⟩})
    (nd : Nonempty {x : (smdl_structure_l I (R := S) my.2.1).Domain //
      (smdl_structure_l I (R := S) my.2.1).mem x ⟨C',right.1.1.output_mem_of_pairMember target.context⟩})
    {n} (φ : Formula 1 n) (closed : φ.FreeClosed)
    (θ : Env (rt_model_l (M := smdl_structure_l I (R := S) my.2.1)
      ⟨C',right.1.1.output_mem_of_pairMember target.context⟩ nd) n)
    (low : ∀ i, Rd_entry_d (θ.bound i).val.val V' S) (valid : Formula.satisfies θ φ) :
    ∃ ρ : Env (rt_model_l (M := smdl_structure_l I (R := R) mx.2.1)
      ⟨C,left.1.1.output_mem_of_pairMember source.context⟩ nc) n,
      (∀ i, Rd_entry_d (ρ.bound i).val.val (θ.bound i).val.val g) ∧ Formula.satisfies ρ φ := by
  let Xn := smdl_structure_l I (R := R) mx.2.1
  let Cn : Xn.Domain := ⟨C,left.1.1.output_mem_of_pairMember source.context⟩
  obtain ⟨a,preimages⟩ := Classical.axiomOfChoice (fun i => (target.image _).mp (low i))
  have values i : ∃ x : (rt_model_l Cn nc).Domain,
      Rd_entry_d (a i) x.val.val j := by
    obtain ⟨x,hx,ax⟩ := source.injection.1.2.2 (a i) (preimages i).1
    have ap := source.root _ _ ax
    have aq := target.root _ _ (preimages i).2
    have member := (right.relation_l I hZF hΩ mb my aq target.context).mpr (θ.bound i).property
    exact ⟨⟨⟨x,hx⟩,(left.relation_l I hZF hΩ mb mx ap source.context).mp member⟩,ap⟩
  obtain ⟨v,points⟩ := Classical.axiomOfChoice values
  have inhabited := nc
  obtain ⟨e⟩ := inhabited
  let ρ : Env (rt_model_l Cn nc) n := ⟨v,fun _ => e⟩
  have targetPoints i := target.root _ _ (preimages i).2
  exact ⟨ρ,fun i => (square (a i) (preimages i).1 _ (points i) _).mpr (targetPoints i),
    (smap_slice_peer_l hZF hΩ mb mx my left right Cn _ ct dt nc nd source.context target.context
      φ closed ρ θ a points targetPoints).mpr valid⟩

/-- 实际表中的三个查询经根方块回到原回答核验，再沿同一完整池图返回。 -/
theorem Tg_root_slice_d.reply_members_l
    {Ω b B R₀ c X R d Y S j k D₀ γ₀ C₀ C C' γ V s γ' V' s' g Γ Dp t : M.Domain}
    (source : Tg_root_slice_d I B R₀ γ₀ D₀ C₀ X R C j γ V s)
    (target : Tg_root_slice_d I B R₀ γ₀ D₀ C₀ Y S C' k γ' V' s')
    (square : Tg_root_square_d D₀ j k g)
    (hΩ : M.IsOmega Ω) (mb : Smdl_d I b B R₀) (mx : Smdl_d I c X R) (my : Smdl_d I d Y S)
    (left : Smap_d I Ω b c B X j) (right : Smap_d I Ω b d B Y k)
    (ct : (smdl_structure_l I (R := R) mx.2.1).TransitiveSet
      ⟨C,left.1.1.output_mem_of_pairMember source.context⟩)
    (nc : Nonempty {x : (smdl_structure_l I (R := R) mx.2.1).Domain //
      (smdl_structure_l I (R := R) mx.2.1).mem x ⟨C,left.1.1.output_mem_of_pairMember source.context⟩})
    (nd : Nonempty {x : (smdl_structure_l I (R := S) my.2.1).Domain //
      (smdl_structure_l I (R := S) my.2.1).mem x ⟨C',right.1.1.output_mem_of_pairMember target.context⟩})
    (hY : (smdl_structure_l I (R := S) my.2.1).Models KP)
    (w u : (smdl_structure_l I (R := S) my.2.1).Domain)
    (omega : (smdl_structure_l I (R := S) my.2.1).IsOmega w)
    (fs : Fs_read_d w ⟨C',right.1.1.output_mem_of_pairMember target.context⟩)
    (kernel : Tg_kernel_d (rt_model_l (M := smdl_structure_l I (R := R) mx.2.1)
      ⟨C,left.1.1.output_mem_of_pairMember source.context⟩ nc))
    (ρ : Env (rt_model_l (M := smdl_structure_l I (R := R) mx.2.1)
      ⟨C,left.1.1.output_mem_of_pairMember source.context⟩ nc) 54)
    (round : Formula.satisfies ρ tg_round0_m)
    (θ : Env (rt_model_l (M := smdl_structure_l I (R := S) my.2.1)
      ⟨C',right.1.1.output_mem_of_pairMember target.context⟩ nd) 7)
    (hw : (θ.bound 0).val = w)
    (hn : (smdl_structure_l I (R := S) my.2.1).mem (θ.bound 3).val w)
    (low : ∀ i : Fin 4, Rd_entry_d (θ.bound (i.castAdd 3)).val.val V' S)
    (valid : Formula.satisfies θ tg_reply_base0_m)
    (pool : M.IsSetInjectionFromTo I t Dp Y) (restrict : M.IsRestrictionOf I g t Γ)
    (pred : ∀ x E, Rd_entry_d x E t → ∀ y,
      Rd_entry_d y E S ↔ ∃ a, Rd_entry_d a x R ∧ Rd_entry_d a y t)
    (points : ∀ i : Fin 4, Rd_entry_d (ρ.bound ([16,17,23,24].get i)).val.val
      (θ.bound (i.castAdd 3)).val.val t)
    (type : Rd_entry_d (ρ.bound 11).val.val u.val t) :
    (smdl_structure_l I (R := S) my.2.1).mem (θ.bound 4).val u ∧
    (smdl_structure_l I (R := S) my.2.1).mem (θ.bound 5).val u ∧
    (smdl_structure_l I (R := S) my.2.1).mem (θ.bound 6).val u := by
  let Yn := smdl_structure_l I (R := S) my.2.1
  let gp : Yn.Domain := ⟨γ',target.rank.1⟩
  let Vp : Yn.Domain := ⟨V',target.rank.2.1⟩
  have rank := (rr_rank_native_l I my.2.1 hY gp Vp).mp target.rank
  have limit : Yn.IsLimitOrdinal gp := (Formula.satisfies_isLimitOrdinal_iff ..).mp
    ((rr_truth_native_l I my.2.1 (Formula.isLimitOrdinal .newest)
      (by simp -implicitDefEqProofs) (fun _ : Fin 1 => gp)).mp target.limit)
  have all := tg_reply_base_scope_l hY omega fs nd θ rank limit hw hn low valid
  obtain ⟨ψ,images,truth⟩ := source.back_l hZF target square hΩ mb mx my left right ct fs.transitive
    nc nd tg_reply_base0_m tg_reply_base0_closed_l θ all valid
  have same (i : Fin 4) : ψ.bound (i.castAdd 3) = ρ.bound ([16,17,23,24].get i) :=
    Subtype.ext (Subtype.ext (pool.2 _ _ _ ((restrict.2 _ _).mp (images (i.castAdd 3))).2 (points i)))
  have compare := kernel.reply_queries_l ρ round
  simp only [tg_reply_compare0_m,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
    Formula.satisfies_conj_iff,Formula.satisfies_mem_iff] at compare
  have members := compare (ψ.bound 4) (ψ.bound 5) (ψ.bound 6) (by
    unfold tg_reply_base_m
    apply (Formula.satisfies_bind ..).mpr
    apply (Formula.closed_env_l tg_reply_base0_m tg_reply_base0_closed_l (ρ := ψ) (η := _) ?_).mp truth
    funext i
    exact Fin.cases (same 0) (Fin.cases (same 1) (Fin.cases (same 2) (Fin.cases (same 3)
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun a => Fin.elim0 a))))))) i)
  have carry i (hi : (smdl_structure_l I (R := R) mx.2.1).mem (ψ.bound i).val (ρ.bound 11).val) :
      Yn.mem (θ.bound i).val u :=
    (pred _ _ type _).mpr ⟨_,hi,((restrict.2 _ _).mp (images i)).2⟩
  exact ⟨carry 4 members.1,carry 5 members.2.1,carry 6 members.2.2⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 所选共同图识别两端的原根切片

根高度由全部前驱实现，根层由固定成员载体实现。同一根交换方块使
这两份完整描述在当前模型中具有相同成员；只用当前外延性识别对象，
不假定原根外部良基，也不调用层解释的外部唯一性。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

/-- 任意 Kuratowski 解释的编码关系由其实现合同与背景外延性确定。 -/
private theorem tg_prepare_codes_l (hE : Extensional M) : I.Codes = KPair_d M := by
  funext p x y
  let ρ : Env M 3 := ⟨fun i => [p,x,y].get i,fun _ => p⟩
  exact propext ((I.realizes ρ (.bound 0) (.bound 1) (.bound 2)).symm.trans
    (kpair_sat_l M hE ρ (.bound 0) (.bound 1) (.bound 2)))

/-- 同一原根方块及完整端点把源 γ、Vγ 的实际共同图像识别为当前保存对象。 -/
theorem Tg_root_slice_d.common_objects_l
    {X₀ R₀ γ₀ D₀ C₀ X R C p γ Vg s Y S C' q γ' Vg' s' L l U V Γ g d : M.Domain}
    (hE : Extensional M) (source : Tg_root_slice_d I X₀ R₀ γ₀ D₀ C₀ X R C p γ Vg s)
    (target : Tg_root_slice_d I X₀ R₀ γ₀ D₀ C₀ Y S C' q γ' Vg' s')
    (common : Ic_common_d I X R Y S L l U V Γ g)
    (square : Tg_root_square_d D₀ p q g)
    (my : Smdl_d I d Y S) (ext : Extensional (smdl_structure_l I (R := S) my.2.1))
    (function : M.IsSetFunction I q)
    (hγ : Rd_entry_d γ U R) (hV : Rd_entry_d Vg U R) :
    Rd_entry_d γ γ' g ∧ Rd_entry_d Vg Vg' g := by
  have eq := tg_prepare_codes_l I hE
  rcases I with ⟨codes,realizes,total,unique,injective⟩
  change codes = KPair_d M at eq
  subst codes
  let I : kpair_convention_l.Interpretation M := ⟨KPair_d M,realizes,total,unique,injective⟩
  let Yn := smdl_structure_l I (R := S) my.2.1
  have current a x (ha : M.mem a D₀) (ax : Rd_entry_d a x q) : Rd_entry_d a x s' := by
    obtain ⟨y,_,ay⟩ := target.injection.1.2.2 a ha
    exact function.2 a y x (target.root a y ay) ax ▸ ay
  obtain ⟨a,ha,ga⟩ := common.injection.1.2.2 γ ((common.carrier γ).mpr ⟨source.rank.1,hγ⟩)
  have height : a = γ' := congrArg Subtype.val
    (ext.eq_of_same_members (⟨a,ha⟩ : Yn.Domain) ⟨γ',target.rank.1⟩ (fun z => by
      constructor
      · intro hz
        obtain ⟨x,hx,xz⟩ := (common.pred γ a ga z.val).mp hz
        obtain ⟨b,hb,bγ,bx⟩ := (source.endpoint.2.2 x).mp hx
        have bD := source.injection.1.input_mem_of_pairMember bx
        have bz := (square b bD x (source.root b x bx) z.val).mp xz
        exact (target.endpoint.2.2 z.val).mpr ⟨b,hb,bγ,current b z.val bD bz⟩
      · intro hz
        obtain ⟨b,hb,bγ,bz⟩ := (target.endpoint.2.2 z.val).mp hz
        have bD := target.injection.1.input_mem_of_pairMember bz
        obtain ⟨x,_,bx⟩ := source.injection.1.2.2 b bD
        exact (common.pred γ a ga z.val).mpr ⟨x,(source.endpoint.2.2 x).mpr ⟨b,hb,bγ,bx⟩,
          (square b bD x (source.root b x bx) z.val).mpr (target.root b z.val bz)⟩))
  obtain ⟨B,hB,vB⟩ := common.injection.1.2.2 Vg ((common.carrier Vg).mpr ⟨source.rank.2.1,hV⟩)
  have layer : B = Vg' := congrArg Subtype.val
    (ext.eq_of_same_members (⟨B,hB⟩ : Yn.Domain) ⟨Vg',target.rank.2.1⟩ (fun z => by
      constructor
      · intro hz
        obtain ⟨x,hx,xz⟩ := (common.pred Vg B vB z.val).mp hz
        obtain ⟨b,hb,bx⟩ := (source.image x).mp hx
        exact (target.image z.val).mpr ⟨b,hb,current b z.val hb
          ((square b hb x (source.root b x bx) z.val).mp xz)⟩
      · intro hz
        obtain ⟨b,hb,bz⟩ := (target.image z.val).mp hz
        obtain ⟨x,_,bx⟩ := source.injection.1.2.2 b hb
        exact (common.pred Vg B vB z.val).mpr ⟨x,(source.image x).mpr ⟨b,hb,bx⟩,
          (square b hb x (source.root b x bx) z.val).mpr (target.root b z.val bz)⟩))
  exact ⟨height ▸ ga,layer ▸ vB⟩

/-- 真实逆图反转根交换方块；只使用同一共同图的单射性。 -/
theorem Tg_root_slice_d.inverse_square_l
    {X₀ R₀ γ₀ D₀ C₀ X R C p γ V s q Y Γ g k : M.Domain}
    (hE : Extensional M) (source : Tg_root_slice_d I X₀ R₀ γ₀ D₀ C₀ X R C p γ V s)
    (square : Tg_root_square_d D₀ p q g) (inj : M.IsSetInjectionFromTo I g Γ Y)
    (inverse : ∀ x y, Rd_entry_d x y k ↔ Rd_entry_d y x g) : Tg_root_square_d D₀ q p k := by
  have eq := tg_prepare_codes_l I hE
  rcases I with ⟨codes,realizes,total,unique,injective⟩
  change codes = KPair_d M at eq
  subst codes
  intro a ha x ax y
  constructor
  · intro xy
    obtain ⟨z,_,az⟩ := source.injection.1.2.2 a ha
    have zx := (square a ha z (source.root a z az) x).mpr ax
    exact inj.2 z y x zx ((inverse x y).mp xy) ▸ source.root a z az
  · intro ay
    exact (inverse x y).mpr ((square a ha y ay x).mpr ax)

end YesMetaZFC.SetTheory.LargeCardinal
