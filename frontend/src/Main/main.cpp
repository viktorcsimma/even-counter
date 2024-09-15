#include "ViewModel/MainViewModel.hpp"
#include "View/MainWindow.h"

#include <QApplication>
#include <QLocale>
#include <QTranslator>

//#include <TinyHsFFI.h>

int main(int argc, char *argv[])
{
    // First, we initialise the Haskell runtime.
    hs_init(&argc, &argv);

    // We put this into a separate block so that
    // everything gets properly destructed
    // before the hs_exit call.
    int exitCode;
    {
        // By constructing the main view model,
        // the HsCalcStateWrapper instance
        // (and this way, the Haskell CalcState object)
        // is also created.
        MainViewModel mainViewModel(DyadicBase, 10);

        QApplication a(argc, argv);

        QTranslator translator;
        const QStringList uiLanguages = QLocale::system().uiLanguages();
        for (const QString &locale : uiLanguages) {
            const QString baseName = "qt-test_" + QLocale(locale).name();
            if (translator.load(":/i18n/" + baseName)) {
                a.installTranslator(&translator);
                break;
            }
        }

        MainWindow w(mainViewModel);
        w.show();

        exitCode = a.exec();
    }

    // We finally shut down the Haskell runtime.
    hs_exit();
    return exitCode;
}
