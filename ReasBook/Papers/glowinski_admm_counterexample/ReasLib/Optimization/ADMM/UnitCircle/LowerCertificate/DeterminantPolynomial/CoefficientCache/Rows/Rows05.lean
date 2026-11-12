/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.CoefficientTree
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.FirstKind512.Context

@[expose] public section

set_option maxRecDepth 8192
set_option linter.style.longLine false

namespace ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.CoefficientCache

def row80Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (1)) (.leaf (0))) (.node 1 (.leaf (-3200)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (1705600)) (.leaf (0))) (.node 1 (.leaf (-362951680)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (41246865920)) (.leaf (0))) (.node 1 (.leaf (-2903779360768)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (138589469491200)) (.leaf (0))) (.node 1 (.leaf (-4763822643609600)) (.leaf (0))))))

def row80Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (123144815337308160)) (.leaf (0))) (.node 1 (.leaf (-2472554723635363840)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (39534848686338080768)) (.leaf (0))) (.node 1 (.leaf (-513439593329065984000)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (5502733032852815872000)) (.leaf (0))) (.node 1 (.leaf (-49304487974361230213120)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (373305408948735028756480)) (.leaf (0))) (.node 1 (.leaf (-2409750777765627495972864)) (.leaf (0))))))

def row80Part02 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (13360513384789265350656000)) (.leaf (0))) (.node 1 (.leaf (-64016149693963538792448000)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (266429118250114918593331200)) (.leaf (0))) (.node 1 (.leaf (-967179388014641923542220800)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (3072654517308054726330286080)) (.leaf (0))) (.node 1 (.leaf (-8564890640579943488028672000)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (20986698208101806559461376000)) (.leaf (0))) (.node 1 (.leaf (-45258270918341287189099315200)) (.leaf (0))))))

def row80Part03 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (85942567648126805992066252800)) (.leaf (0))) (.node 1 (.leaf (-143681941668051998915715661824)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (211296973041252939581934796800)) (.leaf (0))) (.node 1 (.leaf (-272869885520779477531387494400)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (308661909465712889519270789120)) (.leaf (0))) (.node 1 (.leaf (-304740614790104921775831777280)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (261353815396259475285713354752)) (.leaf (0))) (.node 1 (.leaf (-193493041541387237123214540800)) (.leaf (0))))))

def row80Part04 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (122660767405700837819180646400)) (.leaf (0))) (.node 1 (.leaf (-65876552005299470940650864640)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (29554800767961395654673039360)) (.leaf (0))) (.node 1 (.leaf (-10867355313436736787308347392)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (3188777967557727930548224000)) (.leaf (0))) (.node 1 (.leaf (-717799705396186072481792000)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (116359110137908058065469440)) (.leaf (0))) (.node 1 (.leaf (-12089258196146291747061760)) (.leaf (0))))))

def row80Part05 : LookupTree ℤ := (.leaf (604462909807314587353088))

def row80 : CoefficientRow := ⟨81, (.node 48 (.node 16 row80Part00 (.node 16 row80Part01 row80Part02)) (.node 16 row80Part03 (.node 16 row80Part04 row80Part05)))⟩

theorem row80_represents : RowRepresents row80 Data.chebyshevRow80 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row81Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (81))) (.node 1 (.leaf (0)) (.leaf (-88560)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (29012256))) (.node 1 (.leaf (0)) (.leaf (-4514859648))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (408343972608))) (.node 1 (.leaf (0)) (.leaf (-24055172204544)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (993046852546560))) (.node 1 (.leaf (0)) (.leaf (-30226454673702912))))))

def row81Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (704098591222726656))) (.node 1 (.leaf (0)) (.leaf (-12912591708037840896)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (190614449023415746560))) (.node 1 (.leaf (0)) (.leaf (-2305455391350403891200))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (23177511534376060452864))) (.node 1 (.leaf (0)) (.leaf (-195985339698085890097152)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (1407618843742902599811072))) (.node 1 (.leaf (0)) (.leaf (-8657612673343443947225088))))))

def row81Part02 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (45911582358639475477708800))) (.node 1 (.leaf (0)) (.leaf (-211116116526449756146237440)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (845732430769621545642885120))) (.node 1 (.leaf (0)) (.leaf (-2962916855975624200389918720))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (9105549362266552420710481920))) (.node 1 (.leaf (0)) (.leaf (-24604142241340407426947481600)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (58552888000604040300897239040))) (.node 1 (.leaf (0)) (.leaf (-122847317285263610918071173120))))))

def row81Part03 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (227309321779535388909628293120))) (.node 1 (.leaf (0)) (.leaf (-370826187687398908966295568384)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (532827178244593497643878973440))) (.node 1 (.leaf (0)) (.leaf (-673120394873304647528563605504))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (745662191814537980470238380032))) (.node 1 (.leaf (0)) (.leaf (-721692922060125596527594831872)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (607326284138029190520489639936))) (.node 1 (.leaf (0)) (.leaf (-441578762660523016149050327040))))))

def row81Part04 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (275137536734633571600562126848))) (.node 1 (.leaf (0)) (.leaf (-145346288062438720773159911424)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (64185317319985726650039926784))) (.node 1 (.leaf (0)) (.leaf (-23246191383495836613696552960))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (6722642865851155185087283200))) (.node 1 (.leaf (0)) (.leaf (-1492305587518670844689645568)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (238687291510163347681050624))) (.node 1 (.leaf (0)) (.leaf (-24480747847196240787800064))))))

def row81Part05 : LookupTree ℤ := (.node 1 (.leaf (0)) (.leaf (1208925819614629174706176)))

def row81 : CoefficientRow := ⟨82, (.node 48 (.node 16 row81Part00 (.node 16 row81Part01 row81Part02)) (.node 16 row81Part03 (.node 16 row81Part04 row81Part05)))⟩

theorem row81_represents : RowRepresents row81 Data.chebyshevRow81 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row82Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-1)) (.leaf (0))) (.node 1 (.leaf (3362)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-1882720)) (.leaf (0))) (.node 1 (.leaf (420976192)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-50276585216)) (.leaf (0))) (.node 1 (.leaf (3720467305984)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-186699813900288)) (.leaf (0))) (.node 1 (.leaf (6749916348702720)) (.leaf (0))))))

def row82Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-183597724684713984)) (.leaf (0))) (.node 1 (.leaf (3880751906080817152)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-65360032102413762560)) (.leaf (0))) (.node 1 (.leaf (894668491375897477120)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-10113643815553623654400)) (.leaf (0))) (.node 1 (.leaf (95659511043113351118848)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-765276088344906808950784)) (.leaf (0))) (.node 1 (.leaf (5224988465251432695595008)) (.leaf (0))))))

def row82Part02 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-30675738731476153245106176)) (.leaf (0))) (.node 1 (.leaf (155839314411242489747865600)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-688661351303014430885806080)) (.leaf (0))) (.node 1 (.leaf (2658644249553885014827991040)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-8998488229259303127110123520)) (.leaf (0))) (.node 1 (.leaf (26775989365113048329449635840)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-70194982690782621413356339200)) (.leaf (0))) (.node 1 (.leaf (162364046919549367790893793280)) (.leaf (0))))))

def row82Part03 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-331637202218654027828208599040)) (.leaf (0))) (.node 1 (.leaf (598300585227122776734972248064)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-952949348416050757514525933568)) (.leaf (0))) (.node 1 (.leaf (1338524242009966472819145441280)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-1654902699212322184576398000128)) (.leaf (0))) (.node 1 (.leaf (1796064998419180882716308537344)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-1704739659516510668340903018496)) (.leaf (0))) (.node 1 (.leaf (1408145609817445618164193820672)) (.leaf (0))))))

def row82Part04 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-1005818292726746870117281300480)) (.leaf (0))) (.node 1 (.leaf (616151625474566614141775118336)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-320247376892838837200992862208)) (.leaf (0))) (.node 1 (.leaf (139237989953408190087388200960)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-49681160734549401157941329920)) (.leaf (0))) (.node 1 (.leaf (14163085437098496442656358400)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-3100970285175249747444760576)) (.leaf (0))) (.node 1 (.leaf (489463841216472987109163008)) (.leaf (0))))))

def row82Part05 : LookupTree ℤ := (.node 1 (.leaf (-49565958604199796162953216)) (.node 1 (.leaf (0)) (.leaf (2417851639229258349412352))))

def row82 : CoefficientRow := ⟨83, (.node 48 (.node 16 row82Part00 (.node 16 row82Part01 row82Part02)) (.node 16 row82Part03 (.node 16 row82Part04 row82Part05)))⟩

theorem row82_represents : RowRepresents row82 Data.chebyshevRow82 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row83Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-83))) (.node 1 (.leaf (0)) (.leaf (95284)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-32777696))) (.node 1 (.leaf (0)) (.leaf (5356812032))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-508897143040))) (.node 1 (.leaf (0)) (.leaf (31496106816512)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-1366446480347136))) (.node 1 (.leaf (0)) (.leaf (43726287371108352))))))

def row83Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-1071294040592154624))) (.node 1 (.leaf (0)) (.leaf (20674095520199475200)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-321334513228243271680))) (.node 1 (.leaf (0)) (.leaf (4094792374102198845440))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-43404799165483307761664))) (.node 1 (.leaf (0)) (.leaf (387304361784312592334848)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-2938171020432716217712640))) (.node 1 (.leaf (0)) (.leaf (19107589603846309338415104))))))

def row83Part02 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-107263059821591781967921152))) (.node 1 (.leaf (0)) (.leaf (522794745348934735641968640)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-2223055133375650407414497280))) (.node 1 (.leaf (0)) (.leaf (8280205355083394230045900800))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-27102525820785158674930728960))) (.node 1 (.leaf (0)) (.leaf (78156120971566504085846753280)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-198942853382169283127609917440))) (.node 1 (.leaf (0)) (.leaf (447575411124362346499858759680))))))

def row83Part03 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-890583726216843444566045491200))) (.node 1 (.leaf (0)) (.leaf (1567427358141644462436240064512)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-2438725875076695012672930840576))) (.node 1 (.leaf (0)) (.leaf (3350168878893237593166854488064))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-4055467590239182349623034380288))) (.node 1 (.leaf (0)) (.leaf (4313822918898487361960211906560)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-4016805603171050527202295676928))) (.node 1 (.leaf (0)) (.leaf (3257869982295414252477437968384))))))

def row83Part04 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-2286774122188127311835124727808))) (.node 1 (.leaf (0)) (.leaf (1377649539011571949056710148096)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-704680071105663401052025651200))) (.node 1 (.leaf (0)) (.leaf (301722171290312216788472954880))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-106084964334949957500969943040))) (.node 1 (.leaf (0)) (.leaf (29818476461715663730002362368)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-6440627861860662842570571776))) (.node 1 (.leaf (0)) (.leaf (1003408430280142215006126080))))))

def row83Part05 : LookupTree ℤ := (.node 2 (.node 1 (.leaf (0)) (.leaf (-100340843028014221500612608))) (.node 1 (.leaf (0)) (.leaf (4835703278458516698824704))))

def row83 : CoefficientRow := ⟨84, (.node 48 (.node 16 row83Part00 (.node 16 row83Part01 row83Part02)) (.node 16 row83Part03 (.node 16 row83Part04 row83Part05)))⟩

theorem row83_represents : RowRepresents row83 Data.chebyshevRow83 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row84Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (1)) (.leaf (0))) (.node 1 (.leaf (-3528)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (2073288)) (.leaf (0))) (.node 1 (.leaf (-486531584)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (60990209280)) (.leaf (0))) (.node 1 (.leaf (-4738261592064)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (249692027533312)) (.leaf (0))) (.node 1 (.leaf (-9482809309396992)) (.leaf (0))))))

def row84Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (271050299426930688)) (.leaf (0))) (.node 1 (.leaf (-6023339987265126400)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (106708223142812712960)) (.leaf (0))) (.node 1 (.leaf (-1537337517832384020480)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (18303228563758021345280)) (.leaf (0))) (.node 1 (.leaf (-182469109374079966642176)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (1539884811913531993620480)) (.leaf (0))) (.node 1 (.leaf (-11101330506116865131020288)) (.leaf (0))))))

def row84Part02 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (68890917939168771921936384)) (.leaf (0))) (.node 1 (.leaf (-370365434054426053683707904)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (1734250842000883902169743360)) (.leaf (0))) (.node 1 (.leaf (-7104754516305185829656985600)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (25558898939426091587201925120)) (.leaf (0))) (.node 1 (.leaf (-80981041006683365679311093760)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (226507224633915629585049845760)) (.leaf (0))) (.node 1 (.leaf (-560249753683887934046113628160)) (.leaf (0))))))

def row84Part03 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (1226788024467378720827926118400)) (.leaf (0))) (.node 1 (.leaf (-2379468037660809665867063230464)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (4087804064699339682387006062592)) (.leaf (0))) (.node 1 (.leaf (-6215975992163356498165007122432)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (8355240456998797370910106976256)) (.leaf (0))) (.node 1 (.leaf (-9907000178897545581962377297920)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (10332385497313485392261326831616)) (.leaf (0))) (.node 1 (.leaf (-9441756816159546672568785174528)) (.leaf (0))))))

def row84Part04 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (7521558257317575375072157237248)) (.leaf (0))) (.node 1 (.leaf (-5189699869850821237812024573952)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (3075546454915982735314413158400)) (.leaf (0))) (.node 1 (.leaf (-1548598132164734992191439503360)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (653125503315173834734887239680)) (.leaf (0))) (.node 1 (.leaf (-226333014106998411444596244480)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (62737923208606577207449485312)) (.leaf (0))) (.node 1 (.leaf (-13370719564937798672250306560)) (.leaf (0))))))

def row84Part05 : LookupTree ℤ := (.node 2 (.node 1 (.leaf (2056382819164484226175205376)) (.leaf (0))) (.node 1 (.leaf (-203099537695257701350637568)) (.node 1 (.leaf (0)) (.leaf (9671406556917033397649408)))))

def row84 : CoefficientRow := ⟨85, (.node 48 (.node 16 row84Part00 (.node 16 row84Part01 row84Part02)) (.node 16 row84Part03 (.node 16 row84Part04 row84Part05)))⟩

theorem row84_represents : RowRepresents row84 Data.chebyshevRow84 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row85Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (85))) (.node 1 (.leaf (0)) (.leaf (-102340)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (36924272))) (.node 1 (.leaf (0)) (.leaf (-6329875200))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (630877561600))) (.node 1 (.leaf (0)) (.leaf (-40972630000640)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (1865830535413760))) (.node 1 (.leaf (0)) (.leaf (-62691905989902336))))))

def row85Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (1613394639446016000))) (.node 1 (.leaf (0)) (.leaf (-32720775494729728000)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (534750959513868697600))) (.node 1 (.leaf (0)) (.leaf (-7169467409766966886400))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (80011256292999350452224))) (.node 1 (.leaf (0)) (.leaf (-752242580532472525619200)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (6017940644259780204953600))) (.node 1 (.leaf (0)) (.leaf (-41310250616080039600455680))))))

def row85Part02 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (245044895699929325811793920))) (.node 1 (.leaf (0)) (.leaf (-1263525613457786843009384448)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (5691556817377418211753984000))) (.node 1 (.leaf (0)) (.leaf (-22489714387693765889359872000))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (78220323699637341849334579200))) (.node 1 (.leaf (0)) (.leaf (-240118202984933235444468940800)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (651957302650000542297709608960))) (.node 1 (.leaf (0)) (.leaf (-1568074918492138214592086016000))))))

def row85Part03 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (3344159775151600886221897728000))) (.node 1 (.leaf (0)) (.leaf (-6326363433463263794170366525440)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (10614334004475374377446942965760))) (.node 1 (.leaf (0)) (.leaf (-15782120863219950589496868732928))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (20765948504236777091443248332800))) (.node 1 (.leaf (0)) (.leaf (-24127823276693578525884966502400)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (24681576597798021311724949340160))) (.node 1 (.leaf (0)) (.leaf (-22141383614614507597615008317440))))))

def row85Part04 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (17329890636823278061979439202304))) (.node 1 (.leaf (0)) (.leaf (-11757049278713214424680759296000)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (6855772980937628871680851968000))) (.node 1 (.leaf (0)) (.leaf (-3398918435619782201171351961600))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (1412335970965297626970744422400))) (.node 1 (.leaf (0)) (.leaf (-482484504675712486619194851328)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (131916474279073817257469542400))) (.node 1 (.leaf (0)) (.leaf (-27744847560155739559506739200))))))

def row85Part05 : LookupTree ℤ := (.node 3 (.node 1 (.leaf (0)) (.node 1 (.leaf (4213106481356982673851023360)) (.leaf (0)))) (.node 1 (.leaf (-411034778668973919400099840)) (.node 1 (.leaf (0)) (.leaf (19342813113834066795298816)))))

def row85 : CoefficientRow := ⟨86, (.node 48 (.node 16 row85Part00 (.node 16 row85Part01 row85Part02)) (.node 16 row85Part03 (.node 16 row85Part04 row85Part05)))⟩

theorem row85_represents : RowRepresents row85 Data.chebyshevRow85 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row86Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-1)) (.leaf (0))) (.node 1 (.leaf (3698)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-2277968)) (.leaf (0))) (.node 1 (.leaf (560380128)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-73649959680)) (.leaf (0))) (.node 1 (.leaf (6000016715264)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-331637287534592)) (.leaf (0))) (.node 1 (.leaf (13214470380224512)) (.leaf (0))))))

def row86Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-396434111406735360)) (.leaf (0))) (.node 1 (.leaf (9250129266157158400)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-172149774132272168960)) (.leaf (0))) (.node 1 (.leaf (2606839436860121415680)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-32642163383291955118080)) (.leaf (0))) (.node 1 (.leaf (342491621960078667546624)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-3044369972978477044858880)) (.leaf (0))) (.node 1 (.leaf (23137211794636425540927488)) (.leaf (0))))))

def row86Part02 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-151511419171328851122847744)) (.leaf (0))) (.node 1 (.leaf (860455225454284705307295744)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-4261302068916457588188512256)) (.leaf (0))) (.node 1 (.leaf (18487868151060022253164953600)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-70538327714813623365921669120)) (.leaf (0))) (.node 1 (.leaf (237421688405958049377980252160)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-706743630603782100473987727360)) (.leaf (0))) (.node 1 (.leaf (1864164358983889018641532846080)) (.leaf (0))))))

def row86Part03 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-4362937861451655150012098150400)) (.leaf (0))) (.node 1 (.leaf (9067787587964011438310858686464)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-16740530931625867270727739113472)) (.leaf (0))) (.node 1 (.leaf (27444644001114105253058893053952)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-39919482183438698549903844442112)) (.leaf (0))) (.node 1 (.leaf (51438897187371099764848873963520)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-58588032050700642444031259836416)) (.leaf (0))) (.node 1 (.leaf (58804910011755589296018683854848)) (.leaf (0))))))

def row86Part04 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-51804325486546590570302173872128)) (.leaf (0))) (.node 1 (.leaf (39849481143497377361770902978560)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-26589645012342411584675931750400)) (.leaf (0))) (.node 1 (.leaf (15260144094039992735553143439360)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-7450962374554738237077591162880)) (.leaf (0))) (.node 1 (.leaf (3051004956037593665386085089280)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-1027706932560031550445839187968)) (.leaf (0))) (.node 1 (.leaf (277203668123085433187189391360)) (.leaf (0))))))

def row86Part05 : LookupTree ℤ := (.node 3 (.node 1 (.leaf (-57546077939475963345188683776)) (.node 1 (.leaf (0)) (.leaf (8629312500409223049052684288)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-831740963894864872197849088))) (.node 1 (.leaf (0)) (.leaf (38685626227668133590597632)))))

def row86 : CoefficientRow := ⟨87, (.node 48 (.node 16 row86Part00 (.node 16 row86Part01 row86Part02)) (.node 16 row86Part03 (.node 16 row86Part04 row86Part05)))⟩

theorem row86_represents : RowRepresents row86 Data.chebyshevRow86 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row87Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-87))) (.node 1 (.leaf (0)) (.leaf (109736)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-41480208))) (.node 1 (.leaf (0)) (.leaf (7450635456))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-778177480960))) (.node 1 (.leaf (0)) (.leaf (52972663431168)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-2529105110482944))) (.node 1 (.leaf (0)) (.leaf (89120846750351360))))))

def row87Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-2406262862259486720))) (.node 1 (.leaf (0)) (.leaf (51221034027044044800)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-879050507778413035520))) (.node 1 (.leaf (0)) (.leaf (12383146283487209717760))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-145295583059583260688384))) (.node 1 (.leaf (0)) (.leaf (1437225824452629860712448)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-12106680590216734294671360))) (.node 1 (.leaf (0)) (.leaf (87584674205352890682310656))))))

def row87Part02 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-548067734042587028057489408))) (.node 1 (.leaf (0)) (.leaf (2984436064366356253623975936)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-14214160955210333388131008512))) (.node 1 (.leaf (0)) (.leaf (59465450689813810395689779200))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-219296979129264588581177917440))) (.node 1 (.leaf (0)) (.leaf (714961579796849334200429445120)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-2065444563857564743245685063680))) (.node 1 (.leaf (0)) (.leaf (5296403636459916251875151708160))))))

def row87Part03 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-12070035498054911186246094028800))) (.node 1 (.leaf (0)) (.leaf (24461938609391286670792083898368)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-44095395867727108918902421192704))) (.node 1 (.leaf (0)) (.leaf (70671408865448161095614654840832))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-100604912871114174191250937217024))) (.node 1 (.leaf (0)) (.leaf (127005617651435778055582714429440)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-141857640699199306199787469012992))) (.node 1 (.leaf (0)) (.leaf (139751203638125686189652376027136))))))

def row87Part04 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-120938541609916459202583786946560))) (.node 1 (.leaf (0)) (.leaf (91456011565707969148222565253120)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-60035063005622452041032715468800))) (.node 1 (.leaf (0)) (.leaf (33919206623699767672277638840320))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-16314260720074774101125926748160))) (.node 1 (.leaf (0)) (.leaf (6584494416750899817391365029888)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-2187330339399136918149147918336))) (.node 1 (.leaf (0)) (.leaf (582152183806326605933885521920))))))

def row87Part05 : LookupTree ℤ := (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-119305262360308909364228390912))) (.node 1 (.leaf (0)) (.leaf (17669659779487420017505468416)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-1682824740903563811190996992))) (.node 1 (.leaf (0)) (.leaf (77371252455336267181195264)))))

def row87 : CoefficientRow := ⟨88, (.node 48 (.node 16 row87Part00 (.node 16 row87Part01 row87Part02)) (.node 16 row87Part03 (.node 16 row87Part04 row87Part05)))⟩

theorem row87_represents : RowRepresents row87 Data.chebyshevRow87 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row88Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (1)) (.leaf (0))) (.node 1 (.leaf (-3872)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (2497440)) (.leaf (0))) (.node 1 (.leaf (-643340544)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (88551230592)) (.leaf (0))) (.node 1 (.leaf (-7556371677184)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (437582614396928)) (.leaf (0))) (.node 1 (.leaf (-18272680601190400)) (.leaf (0))))))

def row88Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (574675804907438080)) (.leaf (0))) (.node 1 (.leaf (-14062654990676131840)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (274591842186360258560)) (.leaf (0))) (.node 1 (.leaf (-4364940452416947486720)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (57408455950266374553600)) (.leaf (0))) (.node 1 (.leaf (-633082788079245188923392)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (5918821621883736766283776)) (.leaf (0))) (.node 1 (.leaf (-47350572975069894130270208)) (.leaf (0))))))

def row88Part02 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (326680767582034632487469056)) (.leaf (0))) (.node 1 (.leaf (-1956590693539458761422274560)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (10230174197649170095436464128)) (.leaf (0))) (.node 1 (.leaf (-46916190061480689029426970624)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (189469229094441244157301227520)) (.leaf (0))) (.node 1 (.leaf (-676015646664487226540336087040)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (2136666790197480768874846617600)) (.leaf (0))) (.node 1 (.leaf (-5995053486699018505132902973440)) (.leaf (0))))))

def row88Part03 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (14955745134371487653762401566720)) (.leaf (0))) (.node 1 (.leaf (-33207858584073833810803046744064)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (65664408150408440612311906910208)) (.leaf (0))) (.node 1 (.leaf (-115635435736568323090863735439360)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (181262299914335020741133154123776)) (.leaf (0))) (.node 1 (.leaf (-252648722929599448147350748397568)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (312599267353572198555196688695296)) (.leaf (0))) (.node 1 (.leaf (-342520191410154201695593621880832)) (.leaf (0))))))

def row88Part04 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (331306732762797962949606925926400)) (.leaf (0))) (.node 1 (.leaf (-281726564363330295766938476871680)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (209501668143758349881121062256640)) (.leaf (0))) (.node 1 (.leaf (-135330270105284896817618574376960)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (75289375621954273581632868843520)) (.leaf (0))) (.node 1 (.leaf (-35679526396187141867637938585600)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (14196695766061831185228569247744)) (.leaf (0))) (.node 1 (.leaf (-4651864346921359269485485228032)) (.leaf (0))))))

def row88Part05 : LookupTree ℤ := (.node 4 (.node 2 (.node 1 (.leaf (1221850445552129175212959727616)) (.leaf (0))) (.node 1 (.leaf (-247239837221027041777509466112)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (36171060522869704907208785920)) (.leaf (0))) (.node 1 (.leaf (-3404335108034795755972591616)) (.node 1 (.leaf (0)) (.leaf (154742504910672534362390528))))))

def row88 : CoefficientRow := ⟨89, (.node 48 (.node 16 row88Part00 (.node 16 row88Part01 row88Part02)) (.node 16 row88Part03 (.node 16 row88Part04 row88Part05)))⟩

theorem row88_represents : RowRepresents row88 Data.chebyshevRow88 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row89Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (89))) (.node 1 (.leaf (0)) (.leaf (-117480)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (46475088))) (.node 1 (.leaf (0)) (.leaf (-8737316544))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (955279942144))) (.node 1 (.leaf (0)) (.leaf (-68085406785536)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (3404270339276800))) (.node 1 (.leaf (0)) (.leaf (-125666207952732160))))))

def row89Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (3555614472074362880))) (.node 1 (.leaf (0)) (.leaf (-79346344008396308480)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (1428234192151133552640))) (.node 1 (.leaf (0)) (.leaf (-21113027188321104691200))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (260112494960116009795584))) (.node 1 (.leaf (0)) (.leaf (-2703391400611120238559232)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (23944323833984207827238912))) (.node 1 (.leaf (0)) (.leaf (-182285820155492678942851072))))))

def row89Part02 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (1201429269206656293032427520))) (.node 1 (.leaf (0)) (.leaf (-6897617451445273776468525056)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (34674509350508673579003936768))) (.node 1 (.leaf (0)) (.leaf (-153297830812775188454543720448))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (598235437318147076895780372480))) (.node 1 (.leaf (0)) (.leaf (-2066992873125823787281101619200)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (6338778144252526280995378298880))) (.node 1 (.leaf (0)) (.leaf (-17286510609857953262140957655040))))))

def row89Part03 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (41981525766797886493770897162240))) (.node 1 (.leaf (0)) (.leaf (-90877655777538954292398177386496)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (175424212168543990143526235013120))) (.node 1 (.leaf (0)) (.leaf (-301942280338584807277342125719552))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (463129512699784215673517245464576))) (.node 1 (.leaf (0)) (.leaf (-632303063510634674350284211224576)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (767056175406343703310180846403584))) (.node 1 (.leaf (0)) (.leaf (-824791586458434089580839619788800))))))

def row89Part04 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (783552007135512385101797638799360))) (.node 1 (.leaf (0)) (.leaf (-654909140292368560682099518996480)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (479038399293139151803274839982080))) (.node 1 (.leaf (0)) (.leaf (-304579746834269561307514787594240))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (166893011963983321264391664435200))) (.node 1 (.leaf (0)) (.leaf (-77943547209125183552667242201088)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (30580721871522799288606286413824))) (.node 1 (.leaf (0)) (.leaf (-9885880877649045144904855977984))))))

def row89Part05 : LookupTree ℤ := (.node 5 (.node 2 (.node 1 (.leaf (0)) (.leaf (2563006153464567259790147846144))) (.node 1 (.leaf (0)) (.node 1 (.leaf (-512149334221541503572524400640)) (.leaf (0))))) (.node 2 (.node 1 (.leaf (74024945786642973625608568832)) (.leaf (0))) (.node 1 (.leaf (-6886041468524927779126378496)) (.node 1 (.leaf (0)) (.leaf (309485009821345068724781056))))))

def row89 : CoefficientRow := ⟨90, (.node 48 (.node 16 row89Part00 (.node 16 row89Part01 row89Part02)) (.node 16 row89Part03 (.node 16 row89Part04 row89Part05)))⟩

theorem row89_represents : RowRepresents row89 Data.chebyshevRow89 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row90Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-1)) (.leaf (0))) (.node 1 (.leaf (4050)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-2732400)) (.leaf (0))) (.node 1 (.leaf (736290720)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-106025863680)) (.leaf (0))) (.node 1 (.leaf (9466931561472)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-573753427968000)) (.leaf (0))) (.node 1 (.leaf (25081221279744000)) (.leaf (0))))))

def row90Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-826008220812902400)) (.leaf (0))) (.node 1 (.leaf (21173883934824857600)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-433284530203152875520)) (.leaf (0))) (.node 1 (.leaf (7221408836719214592000)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-99634510326908583936000)) (.leaf (0))) (.node 1 (.leaf (1153307777999477208514560)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-11325604423105977243402240)) (.leaf (0))) (.node 1 (.leaf (95239220643038309784748032)) (.leaf (0))))))

def row90Part02 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-691252407893019990373171200)) (.leaf (0))) (.node 1 (.leaf (4359449231952771347487129600)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-24025409100539717648373514240)) (.leaf (0))) (.node 1 (.leaf (116265208762498036187434844160)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-496064890719991621066388668416)) (.leaf (0))) (.node 1 (.leaf (1872486521300781380331896832000)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-6270652536449128343437049856000)) (.leaf (0))) (.node 1 (.leaf (18672609775204071067123659571200)) (.leaf (0))))))

def row90Part03 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-49528766354087394178044316876800)) (.leaf (0))) (.node 1 (.leaf (117170910117669606798344841068544)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-247419719705486349197108261683200)) (.leaf (0))) (.node 1 (.leaf (466483860073656303377916205465600)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-785146860591504635295817405562880)) (.leaf (0))) (.node 1 (.leaf (1178907748329167879494385239326720)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-1577205394374841547255765111144448)) (.leaf (0))) (.node 1 (.leaf (1876632542222841608315955314688000)) (.leaf (0))))))

def row90Part04 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-1980889905679666142111286165504000)) (.leaf (0))) (.node 1 (.leaf (1848830578634355065970533754470400)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-1519319948728495471245320100249600)) (.leaf (0))) (.node 1 (.leaf (1093407068691563200424168254341120)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-684448869290493396196662444032000)) (.leaf (0))) (.node 1 (.leaf (369465550324153784396421267456000)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-170083790184312198290563053649920)) (.leaf (0))) (.node 1 (.leaf (65813308089966957846698058055680)) (.leaf (0))))))

def row90Part05 : LookupTree ℤ := (.node 5 (.node 2 (.node 1 (.leaf (-20993612200850219465022671683584)) (.leaf (0))) (.node 1 (.leaf (5373252144150161561357805158400)) (.node 1 (.leaf (0)) (.leaf (-1060469728965952712052257587200))))) (.node 3 (.node 1 (.leaf (0)) (.node 1 (.leaf (151454226681320743007189729280)) (.leaf (0)))) (.node 1 (.leaf (-13926825441960528092615147520)) (.node 1 (.leaf (0)) (.leaf (618970019642690137449562112))))))

def row90 : CoefficientRow := ⟨91, (.node 48 (.node 16 row90Part00 (.node 16 row90Part01 row90Part02)) (.node 16 row90Part03 (.node 16 row90Part04 row90Part05)))⟩

theorem row90_represents : RowRepresents row90 Data.chebyshevRow90 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row91Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-91))) (.node 1 (.leaf (0)) (.leaf (125580)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-51939888))) (.node 1 (.leaf (0)) (.leaf (10209897984))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-1167331669504))) (.node 1 (.leaf (0)) (.leaf (87019269908480)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-4551777195212800))) (.node 1 (.leaf (0)) (.leaf (175828650512220160))))))

def row91Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-5207630913700167680))) (.node 1 (.leaf (0)) (.leaf (121694111878046023680)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-2294803252557439303680))) (.node 1 (.leaf (0)) (.leaf (35555844861759533875200))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-459381515613933177667584))) (.node 1 (.leaf (0)) (.leaf (5010006956610074655588352)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-46595532680196162314043392))) (.node 1 (.leaf (0)) (.leaf (372764261441569298512347136))))))

def row91Part02 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-2583934084992696273778769920))) (.node 1 (.leaf (0)) (.leaf (15616515915350816471442784256)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-82725327551588108875750965248))) (.node 1 (.leaf (0)) (.leaf (385828248337771260829413408768))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-1590365218758130319028557709312))) (.node 1 (.leaf (0)) (.leaf (5811965915727386547944895283200)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-18880083217150782967869478010880))) (.node 1 (.leaf (0)) (.leaf (54631730160266095396388276797440))))))

def row91Part03 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-141039058474972674849859530915840))) (.node 1 (.leaf (0)) (.leaf (325219476012878167889087859523584)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-670263651579516688537742758379520))) (.node 1 (.leaf (0)) (.leaf (1234910000485897414033174536650752))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-2033423233882793486265152056590336))) (.node 1 (.leaf (0)) (.leaf (2990118560168970433339054689878016)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-3921466964156026797821711068692480))) (.node 1 (.leaf (0)) (.leaf (4578056670904117306212750249164800))))))

def row91Part04 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-4745331818494844669324369969807360))) (.node 1 (.leaf (0)) (.leaf (4352570297561078692623167027937280)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-3517678296750130094293915040481280))) (.node 1 (.leaf (0)) (.leaf (2491393884217395962155851296276480))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-1535790750544970113657716552499200))) (.node 1 (.leaf (0)) (.leaf (816874647857432752345509777113088)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-370748302240147195869732393713664))) (.node 1 (.leaf (0)) (.leaf (141512497057582960838300972089344))))))

def row91Part05 : LookupTree ℤ := (.node 6 (.node 3 (.node 1 (.leaf (0)) (.node 1 (.leaf (-44550230555165006189835491213312)) (.leaf (0)))) (.node 1 (.leaf (11258653622521864626288134717440)) (.node 1 (.leaf (0)) (.leaf (-2194964403718548397730123743232))))) (.node 3 (.node 1 (.leaf (0)) (.node 1 (.leaf (309794494831166413793505837056)) (.leaf (0)))) (.node 1 (.leaf (-28163135893742401253955076096)) (.node 1 (.leaf (0)) (.leaf (1237940039285380274899124224))))))

def row91 : CoefficientRow := ⟨92, (.node 48 (.node 16 row91Part00 (.node 16 row91Part01 row91Part02)) (.node 16 row91Part03 (.node 16 row91Part04 row91Part05)))⟩

theorem row91_represents : RowRepresents row91 Data.chebyshevRow91 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row92Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (1)) (.leaf (0))) (.node 1 (.leaf (-4232)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (2983560)) (.leaf (0))) (.node 1 (.leaf (-840170496)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (126445659648)) (.leaf (0))) (.node 1 (.leaf (-11801594900480)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (747791967784960)) (.leaf (0))) (.node 1 (.leaf (-34184775670169600)) (.leaf (0))))))

def row92Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (1177665521837342720)) (.leaf (0))) (.node 1 (.leaf (-31589145762225192960)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (676672753959244922880)) (.leaf (0))) (.node 1 (.leaf (-11811015341834093199360)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (170746200050427651686400)) (.leaf (0))) (.node 1 (.leaf (-2072070809227343563849728)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (21345618336326126554578944)) (.leaf (0))) (.node 1 (.leaf (-188430286003430634412834816)) (.leaf (0))))))

def row92Part02 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (1436780930776158587397865472)) (.leaf (0))) (.node 1 (.leaf (-9527317401938163895044669440)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (55258440931241350591259082752)) (.leaf (0))) (.node 1 (.leaf (-281715863865674253938936774656)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (1267721387395534142725215485952)) (.leaf (0))) (.node 1 (.leaf (-5053216958817042018389012250624)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (17894584367903901439326840422400)) (.leaf (0))) (.node 1 (.leaf (-56432776209505637002862615592960)) (.leaf (0))))))

def row92Part03 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (158792226674619584970820870471680)) (.leaf (0))) (.node 1 (.leaf (-399249027067614956498063902900224)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (897858671731242684975283980730368)) (.leaf (0))) (.node 1 (.leaf (-1807011163232689680453401722224640)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (3254966861563299463362166478864384)) (.leaf (0))) (.node 1 (.leaf (-5245754216094754852024689352507392)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (7557442514712782413933874490900480)) (.leaf (0))) (.node 1 (.leaf (-9719566470534895203959377452072960)) (.leaf (0))))))

def row92Part04 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (11137003247487900754536786663833600)) (.leaf (0))) (.node 1 (.leaf (-11339494215624044404619273694085120)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (10224460543850652856491654156124160)) (.leaf (0))) (.node 1 (.leaf (-8128763662191823389011998335303680)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (5667236637725285320508365036584960)) (.leaf (0))) (.node 1 (.leaf (-3441047051414094011711854372454400)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (1803833085899177702981582607876096)) (.leaf (0))) (.node 1 (.leaf (-807309912570261349586162845483008)) (.leaf (0))))))

def row92Part05 : LookupTree ℤ := (.node 6 (.node 3 (.node 1 (.leaf (304018606316016141141624615862272)) (.node 1 (.leaf (0)) (.leaf (-94473713254480173941028787585024)))) (.node 1 (.leaf (0)) (.node 1 (.leaf (23577776974009681964628527022080)) (.leaf (0))))) (.node 3 (.node 1 (.leaf (-4541383034118417538467437215744)) (.node 1 (.leaf (0)) (.leaf (633515815104293355679626821632)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-56945241807127492645359714304))) (.node 1 (.leaf (0)) (.leaf (2475880078570760549798248448))))))

def row92 : CoefficientRow := ⟨93, (.node 48 (.node 16 row92Part00 (.node 16 row92Part01 row92Part02)) (.node 16 row92Part03 (.node 16 row92Part04 row92Part05)))⟩

theorem row92_represents : RowRepresents row92 Data.chebyshevRow92 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row93Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (93))) (.node 1 (.leaf (0)) (.leaf (-134044)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (57907008))) (.node 1 (.leaf (0)) (.leaf (-11890238976))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (1420222988800))) (.node 1 (.leaf (0)) (.leaf (-110622459709440)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (6047361130782720))) (.node 1 (.leaf (0)) (.leaf (-244198201852559360))))))

def row93Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (7562961957374853120))) (.node 1 (.leaf (0)) (.leaf (-184872403402496409600)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (3648148760475929149440))) (.node 1 (.leaf (0)) (.leaf (-59177875545427720273920))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (800873915714788481040384))) (.node 1 (.leaf (0)) (.leaf (-9154148575064761783287808)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (89286769352848415423201280))) (.node 1 (.leaf (0)) (.leaf (-749624833448430567338016768))))))

def row93Part02 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (5457495946545013448574500864))) (.node 1 (.leaf (0)) (.leaf (-34671150719227144261532123136)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (193242209414070810058269130752))) (.node 1 (.leaf (0)) (.leaf (-949259976069119768707286958080))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (4125807993549198604478988681216))) (.node 1 (.leaf (0)) (.leaf (-15918399833361470584722919784448)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (54669251952958585846523158855680))) (.node 1 (.leaf (0)) (.leaf (-167497282579277369402113507983360))))))

def row93Part03 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (458623511824211844791501271859200))) (.node 1 (.leaf (0)) (.leaf (-1123717530148108080885215665324032)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (2465980995042002058488310719840256))) (.node 1 (.leaf (0)) (.leaf (-4848932326951276774939977981100032))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (8543356957009392412989485014319104))) (.node 1 (.leaf (0)) (.leaf (-13481626992358480137388433394892800)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (19036351993581591625689460050493440))) (.node 1 (.leaf (0)) (.leaf (-24017189611973907714131505153310720))))))

def row93Part04 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (27019338313470646178397943297474560))) (.node 1 (.leaf (0)) (.leaf (-27031558728809167501861714416107520)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (23966599384451435807277223352729600))) (.node 1 (.leaf (0)) (.leaf (-18748921208601042740179847966883840))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (12870264025995540754674446625669120))) (.node 1 (.leaf (0)) (.leaf (-7698968750685620775769218522021888)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (3978414474038502601832897609465856))) (.node 1 (.leaf (0)) (.leaf (-1756132322198105660010626663055360))))))

def row93Part05 : LookupTree ℤ := (.node 7 (.node 3 (.node 1 (.leaf (0)) (.node 1 (.leaf (652587443187197288473084722937856)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-200206080131482212508345709887488)) (.leaf (0))) (.node 1 (.leaf (49350518351737912326987177787392)) (.leaf (0))))) (.node 3 (.node 1 (.leaf (-9392560563068001490728380268544)) (.node 1 (.leaf (0)) (.leaf (1295194766102329112613208719360)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-115128423653540365565618552832))) (.node 1 (.leaf (0)) (.leaf (4951760157141521099596496896))))))

def row93 : CoefficientRow := ⟨94, (.node 48 (.node 16 row93Part00 (.node 16 row93Part01 row93Part02)) (.node 16 row93Part03 (.node 16 row93Part04 row93Part05)))⟩

theorem row93_represents : RowRepresents row93 Data.chebyshevRow93 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row94Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-1)) (.leaf (0))) (.node 1 (.leaf (4418)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-3251648)) (.leaf (0))) (.node 1 (.leaf (955984512)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-150226137600)) (.leaf (0))) (.node 1 (.leaf (14642040878080)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-969036887203840)) (.leaf (0))) (.node 1 (.leaf (46279497931735040)) (.leaf (0))))))

def row94Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-1666061925542461440)) (.leaf (0))) (.node 1 (.leaf (46715069676974899200)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-1046417560764237742080)) (.leaf (0))) (.node 1 (.leaf (19107312862785951498240)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-289101951141283092234240)) (.leaf (0))) (.node 1 (.leaf (3673818640656920525930496)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-39653915486455650121154560)) (.leaf (0))) (.node 1 (.leaf (367003824709127465259237376)) (.leaf (0))))))

def row94Part02 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-2936030597673019722073899008)) (.leaf (0))) (.node 1 (.leaf (20442309295028190792193671168)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-124600742369695639114323329024)) (.leaf (0))) (.node 1 (.leaf (668200282693815874055475036160)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-3166241339533773680139789402112)) (.leaf (0))) (.node 1 (.leaf (13304832945915439227346989613056)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-49731384034626842608772679991296)) (.leaf (0))) (.node 1 (.leaf (165771280115422808695908933304320)) (.leaf (0))))))

def row94Part03 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-493786791833174323775047886438400)) (.leaf (0))) (.node 1 (.leaf (1316496050716038646081066446618624)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-3145293732027458846745715311378432)) (.leaf (0))) (.node 1 (.leaf (6738973153316693797430023161905152)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-12952831515465853013242122441064448)) (.leaf (0))) (.node 1 (.leaf (22332468130113539678003659381145600)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-34520696499429742688710741280686080)) (.leaf (0))) (.node 1 (.leaf (47792270457698078455338297553059840)) (.leaf (0))))))

def row94Part04 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-59171382471435716182799796970455040)) (.leaf (0))) (.node 1 (.leaf (65378170842565336761415160289034240)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-64287578001468987860215082988339200)) (.leaf (0))) (.node 1 (.leaf (56061962431094695003566445040762880)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-43165079054927370800868060970352640)) (.leaf (0))) (.node 1 (.leaf (29181575103405175521060747623792640)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-17201770587270419254520019651919872)) (.leaf (0))) (.node 1 (.leaf (8764138860647266553251958064414720)) (.leaf (0))))))

def row94Part05 : LookupTree ℤ := (.node 7 (.node 3 (.node 1 (.leaf (-3816283250712227461162877941972992)) (.node 1 (.leaf (0)) (.leaf (1399648599628874750887198233460736)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-423989937236974106981319946797056))) (.node 1 (.leaf (0)) (.leaf (103242419737594242192441792790528))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-19418636941240296337136387358720))) (.node 1 (.leaf (0)) (.leaf (2647334774011785717871777153024)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-232732727385651491681035354112))) (.node 1 (.leaf (0)) (.leaf (9903520314283042199192993792))))))

def row94 : CoefficientRow := ⟨95, (.node 48 (.node 16 row94Part00 (.node 16 row94Part01 row94Part02)) (.node 16 row94Part03 (.node 16 row94Part04 row94Part05)))⟩

theorem row94_represents : RowRepresents row94 Data.chebyshevRow94 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row95Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-95))) (.node 1 (.leaf (0)) (.leaf (142880)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-64410304))) (.node 1 (.leaf (0)) (.leaf (13802208000))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-1720675264000))) (.node 1 (.leaf (0)) (.leaf (139906541465600)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-7985434905190400))) (.node 1 (.leaf (0)) (.leaf (336757197716029440))))))

def row95Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-10895085808459776000))) (.node 1 (.leaf (0)) (.leaf (278302542756446208000)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-5740983882004404633600))) (.node 1 (.leaf (0)) (.leaf (97392501270999623270400))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-1379077817997354665508864))) (.node 1 (.leaf (0)) (.leaf (16501785856378602835148800)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-168594600325759715665510400))) (.node 1 (.leaf (0)) (.leaf (1483632482866685497856491520))))))

def row95Part02 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-11329557141891052892722298880))) (.node 1 (.leaf (0)) (.leaf (75555769309283525845919465472)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-442443694153462088286915788800))) (.node 1 (.leaf (0)) (.leaf (2285660541456751516818237030400))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-10458290672616745964758567485440))) (.node 1 (.leaf (0)) (.leaf (42528065725192349039416899010560)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-154132020022212271064068518838272))) (.node 1 (.leaf (0)) (.leaf (499039842810122986793931374592000))))))

def row95Part03 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-1446197095490560492341597044736000))) (.node 1 (.leaf (0)) (.leaf (3756709631580185373047348558561280)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-8756568459096919751979741342597120))) (.node 1 (.leaf (0)) (.leaf (18326878633584664369800024304910336))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-34449019987941098439473729896448000))) (.node 1 (.leaf (0)) (.leaf (58146563252585559493395752157184000)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-88077744992441077003110942611865600))) (.node 1 (.leaf (0)) (.leaf (119601730527370064624808100259430400))))))

def row95Part04 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-145362103256342078543997537238384640))) (.node 1 (.leaf (0)) (.leaf (157787900413939841024692034994176000)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-152541755387389411527707389329408000))) (.node 1 (.leaf (0)) (.leaf (130872846070790432747312738048409600))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-99200422135850282356410568566374400))) (.node 1 (.leaf (0)) (.leaf (66062118957495971817890713769607168)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-38381955648579341110872936913305600))) (.node 1 (.leaf (0)) (.leaf (19284410043492638766514542791884800))))))

def row95Part05 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-8285153944611652210798840606883840))) (.node 1 (.leaf (0)) (.leaf (2999503279389231714282742176808960)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-897330392825686126289627071381504))) (.node 1 (.leaf (0)) (.leaf (215877400038256485875611965849600))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-40132468648582921786885983436800))) (.node 1 (.leaf (0)) (.leaf (5409797971677111801309172858880)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-470417214928444504461667205120))) (.node 1 (.leaf (0)) (.leaf (19807040628566084398385987584))))))

def row95 : CoefficientRow := ⟨96, (.node 48 (.node 16 row95Part00 (.node 16 row95Part01 row95Part02)) (.node 16 row95Part03 (.node 16 row95Part04 row95Part05)))⟩

theorem row95_represents : RowRepresents row95 Data.chebyshevRow95 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

end ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.CoefficientCache
